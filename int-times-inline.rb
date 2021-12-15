def test
  2.times {
    puts *caller(0) # TODO handle side exits.

    puts "inside block for times"
  }
end

test
test
