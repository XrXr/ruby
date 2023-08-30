# frozen_string_literal: true

require_relative "test_helper"

class YARPRubyAPITest < Test::Unit::TestCase
  def test_ruby_api
    filepath = __FILE__
    source = File.read(filepath, binmode: true, external_encoding: Encoding::UTF_8)

    assert_equal YARP.lex(source, filepath).value, YARP.lex_file(filepath).value
    assert_equal YARP.dump(source, filepath), YARP.dump_file(filepath)

    serialized = YARP.dump(source, filepath)
    ast1 = YARP.load(source, serialized).value
    ast2 = YARP.parse(source, filepath).value
    ast3 = YARP.parse_file(filepath).value

    assert_equal_nodes ast1, ast2
    assert_equal_nodes ast2, ast3
  end

  def test_literal_value_method
    assert_equal 123, parse_expression("123").value
    assert_equal 3.14, parse_expression("3.14").value
    assert_equal 42i, parse_expression("42i").value
    assert_equal 42.1ri, parse_expression("42.1ri").value
    assert_equal 3.14i, parse_expression("3.14i").value
    assert_equal 42r, parse_expression("42r").value
    assert_equal 0.5r, parse_expression("0.5r").value
    assert_equal 42ri, parse_expression("42ri").value
    assert_equal 0.5ri, parse_expression("0.5ri").value
  end

  def test_location_join
    recv, args_node, _ = parse_expression("1234 + 567").child_nodes
    arg = args_node.arguments[0]

    joined = recv.location.join(arg.location)
    assert_equal 0, joined.start_offset
    assert_equal 10, joined.length

    e = assert_rais RuntimeError do
      arg.location.join(recv.location)
    end
    assert_equal "Incompatible locations", e.message

    other_recv, other_args_node, _ = parse_expression("1234 + 567").child_nodes
    other_arg = other_args_node.arguments[0]

    e = assert_rais RuntimeError do
      other_arg.location.join(recv.location)
    end
    assert_equal "Incompatible sources", e.message

    e = assert_rais RuntimeError do
      recv.location.join(other_arg.location)
    end
    assert_equal "Incompatible sources", e.message
  end

  private

  def parse_expression(source)
    YARP.parse(source).value.statements.body.first
  end
end
