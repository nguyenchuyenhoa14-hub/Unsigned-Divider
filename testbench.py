import cocotb, json, sys, random

from pathlib import Path
from cocotb.runner import get_runner, get_results
from cocotb.triggers import Timer

# directory for this homework
PROJECT_PATH = Path(__file__).resolve().parent

p = Path.cwd() / '..' / 'common' / 'python'
sys.path.append(str(p))
import cocotb_utils as cu
from cocotb_utils import assertEquals

# for deterministic random numbers
random.seed(12345)

# --- SỬA 1: Thêm 'test_' vào tên hàm để Pytest chạy nó ---
def test_1iter(pytestconfig): 
    """run 1iter tests"""

    verilog_sources = [ PROJECT_PATH / "divu_1iter.v" ]
    toplevel_module = "divu_1iter"

    runr = get_runner(cu.SIM)
    runr.build(
        verilog_sources=verilog_sources,
        vhdl_sources=[],
        hdl_toplevel=toplevel_module,
        includes=[PROJECT_PATH],
        build_dir="sim_build_1iter",
        build_args=["-CFLAGS", "-Wno-error"],
    )

    runr.test(
        seed=12345,
        waves=True,
        hdl_toplevel=toplevel_module, 
        test_module="testbench_1iter", 
        testcase=None,
    )
    pass

# --- SỬA 2: Thêm 'test_' vào tên hàm để Pytest chạy nó ---
def test_divider(pytestconfig):
    """run divider tests"""

    verilog_sources = [ PROJECT_PATH / "divider_unsigned.v",
                        PROJECT_PATH / "divu_1iter.v"
			]

    toplevel_module = "divider_unsigned"

    runr = get_runner(cu.SIM)
    runr.build(
        verilog_sources=verilog_sources,
        vhdl_sources=[],
        hdl_toplevel=toplevel_module,
        includes=[PROJECT_PATH],
        build_dir=cu.SIM_BUILD_DIR,
        build_args=["-CFLAGS", "-Wno-error"],
    )

    runr.test(
        seed=12345,
        waves=True,
        hdl_toplevel=toplevel_module, 
        test_module=Path(__file__).stem, 
        testcase=None,
    )
    pass

def runCocotbTests(pytestconfig):
    """calculate scores for autograder"""
    # Lưu ý: Hàm get_results có thể cần điều chỉnh tùy vào file cocotb_utils của bạn
    # Nhưng logic cơ bản giữ nguyên
    test_results = cu.aggregateTestResults(
        get_results(Path(cu.SIM_BUILD_DIR,'test_1iter.None')), # Sửa tên file xml khớp với tên hàm test
        get_results(Path(cu.SIM_BUILD_DIR,'test_divider.None')),
    )
    # 1 point per cocotb test
    points = { 'pointsEarned': test_results['tests_passed'], 'pointsPossible': test_results['tests_total'] }
    with open(cu.POINTS_FILE, 'w') as f:
        json.dump(points, f, indent=2)
        pass
    pass


#########################
## TEST CASES ARE HERE ##
#########################

# --- SỬA 3: Đổi tên các hàm bên dưới (bỏ 'test_' hoặc đổi thành 'simple_') ---
# Pytest sẽ bỏ qua, nhưng Cocotb vẫn chạy nhờ @cocotb.test()

@cocotb.test()
async def simple0(dut): # Đã đổi từ test_simple0 -> simple0
    await Timer(1, "ns")
    dut.i_dividend.value = 4
    dut.i_divisor.value = 2
    await Timer(1, "ns")
    assertEquals(2, dut.o_quotient.value)
    assertEquals(0, dut.o_remainder.value)

@cocotb.test()
async def simple1(dut): # Đã đổi từ test_simple1 -> simple1
    await Timer(1, "ns")
    dut.i_dividend.value = 4
    dut.i_divisor.value = 4
    await Timer(1, "ns")
    assertEquals(1, dut.o_quotient.value)
    assertEquals(0, dut.o_remainder.value)

@cocotb.test()
async def simple2(dut): # Đã đổi từ test_simple2 -> simple2
    await Timer(1, "ns")
    dut.i_dividend.value = 10
    dut.i_divisor.value = 4
    await Timer(1, "ns")
    assertEquals(2, dut.o_quotient.value)
    assertEquals(2, dut.o_remainder.value)

@cocotb.test()
async def simple3(dut): # Đã đổi từ test_simple3 -> simple3
    await Timer(1, "ns")
    dut.i_dividend.value = 2
    dut.i_divisor.value = 4
    await Timer(1, "ns")
    assertEquals(0, dut.o_quotient.value)
    assertEquals(2, dut.o_remainder.value)

@cocotb.test()
async def random1k(dut): # Đã đổi từ test_random1k -> random1k
    for i in range(1000):
        await Timer(1, "ns")
        dividend = random.randrange(0,2**32)
        divisor = random.randrange(1,2**32) # NB: no divide-by-zero
        dut.i_dividend.value = dividend
        dut.i_divisor.value = divisor
        await Timer(1, "ns")

        exp_quotient = int(dividend / divisor)
        exp_remainder = dividend % divisor

        msg = f'expected {dividend} / {divisor} = {exp_quotient} rem {exp_remainder}\n'
        msg += f'but was quot={dut.o_quotient.value} rem={dut.o_remainder.value}'
        assertEquals(exp_quotient, dut.o_quotient.value, msg)
        assertEquals(exp_remainder, dut.o_remainder.value, msg)
        pass
    pass