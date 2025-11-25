import os

# --- Cấu hình cơ bản ---
# Mặc định sử dụng Icarus Verilog
SIM = os.getenv("SIM", "icarus")
SIM_BUILD_DIR = "sim_build"
VERILATOR_FLAGS = ["--vpi", "--public-flat-rw", "--prefix Vtop", "-LDFLAGS -Wl,-rpath,$(cocotb-config --lib-dir)"]
POINTS_FILE = "points.json"

# --- Hàm assertEquals ---
# Đây là hàm quan trọng nhất mà code của bạn đang gọi
def assertEquals(expected, actual, msg=""):
    """
    Hàm thay thế cho assert, cung cấp thông báo lỗi rõ ràng hơn.
    """
    # Chuyển đổi đối tượng cocotb value thành integer để so sánh
    try:
        actual_val = int(actual)
    except (ValueError, TypeError):
        actual_val = actual

    assert expected == actual_val, f"Assertion Failed: Expected {expected}, got {actual}. {msg}"

# --- Các hàm phụ trợ khác (có thể cần sau này) ---
def get_results(path):
    """Hàm giả để tránh lỗi khi gọi aggregateTestResults."""
    # Trong trường-hợp thực tế, nó sẽ đọc file kết quả XML.
    # Bây giờ, chúng ta chỉ cần nó trả về một dictionary rỗng.
    return {'tests_total': 0, 'tests_passed': 0}

def aggregateTestResults(*args):
    """Hàm giả để tránh lỗi."""
    return {'tests_total': 0, 'tests_passed': 0}
