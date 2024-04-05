#
# IMPORTANT: Always keep the first 7 lines (comments),
# even if this file is otherwise empty.
#
# This test file includes tests which point out known bugs.
# So all tests will cause failure.
#
assert_equal "[1, 2, 3, 4]", %q{
  def foo(*b) = b

  def forward(...)
    splat = [1,2,3]
    foo(*splat, ...)
  end

  forward(4)
}
