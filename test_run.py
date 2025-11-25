import pytest
from testbench import runCocotbTestsDivider, runCocotbTests1iter # Import hàm điều khiển từ file của bạn

# Đánh dấu đây là một test case của pytest
# Hàm này sẽ được pytest tìm thấy và chạy
def test_divider_unsigned(pytestconfig):
    """
    Đây là test case duy nhất mà pytest sẽ chạy trực tiếp.
    Nhiệm vụ của nó là gọi hàm điều khiển của cocotb.
    """
    runCocotbTestsDivider(pytestconfig)
def test_1iter_divider(pytestconfig):
    """
    Test này sẽ gọi hàm điều khiển để kiểm tra module 'divu_1iter'.
    """
    runCocotbTests1iter(pytestconfig)
