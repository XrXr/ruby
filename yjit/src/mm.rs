//! Memory management stuff for YJIT's code buffer. Deals with virtual memory
// I'm aware that there is an experiment in Rust Nightly right now for to see if banning
// usize->pointer casts is viable. It seems like a lot of work for us to participate for not much
// benefit.

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;

use crate::utils::IntoUsize;

#[cfg(not(test))]
use crate::cruby::{
    rb_yjit_get_page_size, rb_yjit_mark_executable, rb_yjit_mark_writable,
    rb_yjit_reserve_addr_space,
};

/// A buffer for generated executable machine code. Normally there is only a single buffer per YJIT
/// process so this is designed for such situation. We reserve address space for the entire buffer
/// upfront and map physical memory into the reserved address space as needed. On Linux, this is
/// basically done with an `mmap` with `PROT_NONE` upfront and gradually using `mprotect` with
/// `PROT_READ|PROT_WRITE` as needed. The WIN32 equivalent seems to be `VirtualAlloc` with
/// `MEM_RESERVE` and later with `MEM_COMMIT`.
///
/// The buffer handles ["W^X"](https://en.wikipedia.org/wiki/W%5EX) semi-automatically. Writes
/// are always accepted and once writes are done a call to [Self::mark_all_executable] makes the
/// the entire buffer executable.
pub struct CodeBuffer {
    /// Location of the virtual memory buffer.
    region_start: *mut u8,

    /// Number of bytes per "page", memory protection permission can only be controlled at this
    /// granularity.
    page_size_bytes: usize,

    /// On the first write to a page, we reserve memory for it and keep track of that.
    /// Could use a syscall to check whether a page is mapped instead, but that has portability
    /// costs. We use this information to change mapped pages to executable.
    ///
    /// Two entries in this sorted map tells us whether a range is mapped or not and this
    /// starts off with two elements marking off the start and the end of the buffer.
    /// The keys are page indicies relative to [Self::region_start].
    mapped_ranges: RefCell<BTreeMap<usize, PageOnwards>>,

    /// Keep track of the address of the last written to page.
    /// Used for changing protection to implement W^X.
    current_write_page: Cell<Option<usize>>,

    // During normal execution we use mmap(2) but when testing we don't
    // link with Ruby so can't test that code path. This member provides ownership over some
    // memory so we can stub out enough and have some unit tests.
    // `region_start` points to this during testing.
    //
    // Alan frankly finds this practice questionable since it introduces a lot of testing specific
    // complexity that obscures what happens during normal operation. So much of normal execution
    // is stubbed out that we're barely testing much. The stubbing itself is also somewhat brittle
    // and adds maintenance burden if we decide to add new inputs that require stubbing (think
    // things that require peeking at runtime values). It seems that we're paying a lot in total
    // complexity for not that much additional confidence from unit testing. It might be a better
    // trade-off to simply delete all the existing Rust codegen tests.
    #[cfg(test)]
    _testing_owned_memory: Vec<u8>,
}

/// Status of a page and onwards. See [CodeBuffer::mapped_ranges].
#[derive(Clone, Copy, PartialEq)]
enum PageOnwards {
    Mapped,
    NotMapped,
}

/// Pointer into a [CodeBuffer].
/// We may later change this to wrap an u32.
/// Note: there is no NULL constant for CodePtr. You should use Option<CodePtr> instead.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Debug)]
#[repr(C)]
pub struct CodePtr(*const u8);

/// Errors that can happen when writing to [CodeBuffer]
#[derive(Debug)]
pub enum WriteError {
    OutOfBounds,
    FailedPageMapping,
}

use WriteError::*;

impl CodeBuffer {
    /// Reserve part of the address space for the code buffer. On POSIX systems,
    /// this is basically mmap with `PROT_NONE`.
    #[cfg(not(test))]
    pub fn new(max_mem_size: u32) -> Option<Self> {
        // 2 GiB. It's likely a bug if we generate this much code.
        const MAX_BUFFER_SIZE: u32 = 2 * 1024 * 1024 * 1024;
        if max_mem_size > MAX_BUFFER_SIZE {
            return None;
        }

        let page_size = unsafe { rb_yjit_get_page_size() };
        let num_pages = max_mem_size / page_size;
        let mem_block: *mut u8 = unsafe { rb_yjit_reserve_addr_space(max_mem_size) };

        // The start of the buffer should be page aligned
        if page_size == 0 || (mem_block as usize % page_size.as_usize()) != 0 {
            return None;
        }

        let mut mapped_ranges = BTreeMap::new();
        mapped_ranges.insert(0, PageOnwards::NotMapped);
        mapped_ranges.insert(num_pages.as_usize(), PageOnwards::NotMapped);

        Some(CodeBuffer {
            region_start: mem_block,
            page_size_bytes: page_size.as_usize(),
            mapped_ranges: RefCell::new(mapped_ranges),
            current_write_page: Cell::new(None),
        })
    }

    /// Stubbed FFI-free version for testing
    #[cfg(test)]
    pub fn new(max_mem_size: u32) -> Self {
        let page_size_bytes = 4096;
        let num_pages = max_mem_size.as_usize() / page_size_bytes;
        let mut mem_block = vec![0; max_mem_size.as_usize()];

        let mut mapped_ranges = BTreeMap::new();
        mapped_ranges.insert(0, PageOnwards::NotMapped);
        mapped_ranges.insert(num_pages, PageOnwards::NotMapped);

        CodeBuffer {
            region_start: mem_block.as_mut_ptr(),
            page_size_bytes,
            mapped_ranges: RefCell::new(mapped_ranges),
            _testing_owned_memory: mem_block,
            current_write_page: Cell::new(None),
        }
    }

    /// Return the start of the buffer as a raw pointer. Note that it could be a dangling
    /// pointer so be careful dereferencing it.
    pub fn start_ptr(&self) -> CodePtr {
        CodePtr(self.region_start)
    }

    /// Write a single byte into the buffer. The first write to a page makes it readable.
    pub fn write_byte(&self, write_ptr: CodePtr, byte: u8) -> Result<(), WriteError> {
        let page_size = self.page_size_bytes;
        let raw: *const u8 = write_ptr.raw_ptr();
        let page_addr = (raw as usize / page_size) * page_size;

        if self.current_write_page.get() == Some(page_addr) {
            // Writing within the last written to page, nothing to do
        } else {
            let page_idx = {
                // `self.region_start` is page aligned (checked in [Self::new]).
                // Can't use `offset_from` because `write_ptr` might be dangling.
                let offset_from_start = (raw as usize).checked_sub(self.region_start as usize).ok_or(OutOfBounds)?;

                offset_from_start / page_size
            };

            // Find range info that starts with index smaller or equal the query page index
            let mut mapped_ranges = self.mapped_ranges.borrow_mut();
            let (_, &lower_status) = mapped_ranges
                .range(..=page_idx)
                .next_back()
                .expect("zero sentinal guarantees this lookup");

            if lower_status == PageOnwards::Mapped {
                // Writing to a page we've written to before
                #[cfg(not(test))]
                {
                    let page_ptr = page_addr as *mut _;
                    let page_size = self.page_size_bytes.try_into().unwrap();
                    unsafe {
                        if !rb_yjit_mark_writable(page_ptr, page_size) {
                            // Can happen with ENOMEM, for example
                            return Err(FailedPageMapping);
                        }
                    }
                }
                self.current_write_page.set(Some(page_addr));
            } else {
                // Writing to a page for the first time
                //
                // Fill the executable memory with PUSH DS (0x1E) so that executing uninitialized
                // memory will fault with #UD in 64-bit mode. On Linux, this translates to SIGILL
                // to crash using the usual crash reporter.
                #[cfg(not(test))]
                {
                    let page_ptr = page_addr as *mut u8;
                    let page_size = self.page_size_bytes.try_into().unwrap();
                    unsafe {
                        if !rb_yjit_mark_writable(page_ptr.cast(), page_size) {
                            // Can happen with ENOMEM, for example
                            return Err(FailedPageMapping);
                        }
                        std::slice::from_raw_parts_mut(page_ptr, self.page_size_bytes).fill(0x1E);
                    }
                }

                // Bounds check
                let (&end_of_buffer, _) = mapped_ranges
                    .iter().next_back().expect("sential from constructor");
                if page_idx >= end_of_buffer {
                    return Err(OutOfBounds);
                }

                // Adjust markers in `mapped_ranges` Add a single new page at `page_idx`
                //
                // ... insert a `PageOnwards::Mapped` at `page_idx` to start the range
                let at_page_idx = mapped_ranges.insert(page_idx, PageOnwards::Mapped);
                assert_eq!(
                    false,
                    matches!(at_page_idx, Some(PageOnwards::Mapped)),
                    "initial lookup should catch this",
                );

                // ... adjust adjacent marker so we're adding exactly one page
                use std::collections::btree_map::Entry::*;
                match mapped_ranges.entry(page_idx + 1) {
                    Vacant(adjacent) => {
                        // a Mapped followed by a NotMapped -- one new mapped page
                        adjacent.insert(PageOnwards::NotMapped);
                    }
                    Occupied(adjacent) => {
                        match adjacent.get() {
                            // Extending a range by adding a page to its left
                            PageOnwards::Mapped => { adjacent.remove(); }
                            // Already what we want
                            PageOnwards::NotMapped => ()
                        }
                    }
                }

                self.current_write_page.set(Some(page_addr));
            }
        }

        unsafe { (write_ptr.raw_ptr() as *mut u8).write(byte) };

        Ok(())
    }

    /// Make the entire code buffer executable. Call this at the end of a write session.
    /// See [Self] for usual usage flow.
    pub fn mark_all_executable(&self) {
        self.current_write_page.set(None);

        // Mark all pages we've written to as executable
        let page_size = self.page_size_bytes;
        let region_start = self.region_start;
        let mapped_ranges = self.mapped_ranges.borrow();
        let mut iter = mapped_ranges.iter().peekable();

        loop {
            match iter.next() {
                None => { break; }
                Some((_, PageOnwards::NotMapped)) => (), // continue
                Some((page_idx, PageOnwards::Mapped)) => {
                    // Look at the next marker to find the region size
                    let (&next_page_idx, _) = iter.peek().expect("end sentinal");
                    let region_size = (next_page_idx - page_idx) * page_size;
                    let region_size: u32 = region_size.try_into().unwrap();
                    let region_ptr = region_start.wrapping_add(page_idx * page_size);

                    // Make this region executable
                    #[cfg(not(test))]
                    unsafe { rb_yjit_mark_executable(region_ptr.cast(), region_size); }

                    // silence dead code warnings in test builds
                    let _ = (region_size, region_ptr, FailedPageMapping);
                }
            }
        }
    }
}

impl CodePtr {
    /// Note that the raw pointer might be dangling if there hasn't
    /// been any writes to it through the CodeBuffer yet.
    pub fn raw_ptr(self) -> *const u8 {
        let CodePtr(ptr) = self;
        return ptr;
    }

    /// Advance the CodePtr. Might make it dangling.
    pub fn add_bytes(self, bytes: usize) -> Self {
        let CodePtr(raw) = self;
        CodePtr(raw.wrapping_add(bytes))
    }

    pub fn into_i64(self) -> i64 {
        let CodePtr(ptr) = self;
        ptr as i64
    }

    pub fn into_usize(self) -> usize {
        let CodePtr(ptr) = self;
        ptr as usize
    }
}

impl From<*mut u8> for CodePtr {
    fn from(value: *mut u8) -> Self {
        assert!(value as usize != 0);
        return CodePtr(value);
    }
}
