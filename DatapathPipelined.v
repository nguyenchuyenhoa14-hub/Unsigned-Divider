`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31
// inst are 32 bits in RV32IM
`define INST_SIZE 31
// RV opcodes are 7 bits
`define OPCODE_SIZE 6
`define DIVIDER_STAGES 8

`include "cla.v"
`include "DividerUnsignedPipelined.v"

module RegFile (
  input      [        4:0] rd,
  input      [`REG_SIZE:0] rd_data,
  input      [        4:0] rs1,
  output reg [`REG_SIZE:0] rs1_data,
  input      [        4:0] rs2,
  output reg [`REG_SIZE:0] rs2_data,
  input                    clk,
  input                    we,
  input                    rst
);
  localparam NumRegs = 32;
  reg [`REG_SIZE:0] regs[0:NumRegs-1];

  integer i;
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      for (i = 0; i < NumRegs; i = i + 1) begin
        regs[i] <= 32'd0;
      end
    end else if (we && rd != 5'd0) begin
      regs[rd] <= rd_data;
    end
  end

  always @(*) begin
    rs1_data = (rs1 == 5'd0) ? 32'd0 : regs[rs1];
    rs2_data = (rs2 == 5'd0) ? 32'd0 : regs[rs2];
    if (we && rd != 5'd0) begin
      if (rd == rs1) rs1_data = rd_data;
      if (rd == rs2) rs2_data = rd_data;
    end
  end
endmodule

module DatapathPipelined (
  input                     clk,
  input                     rst,
  output     [ `REG_SIZE:0] pc_to_imem,
  input      [`INST_SIZE:0] inst_from_imem,
  output reg [ `REG_SIZE:0] addr_to_dmem,
  input      [ `REG_SIZE:0] load_data_from_dmem,
  output reg [ `REG_SIZE:0] store_data_to_dmem,
  output reg [         3:0] store_we_to_dmem,
  output reg                halt,
  output reg [ `REG_SIZE:0] trace_writeback_pc,
  output reg [`INST_SIZE:0] trace_writeback_inst
);
  localparam [`OPCODE_SIZE:0] OpcodeLoad    = 7'b00_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeStore   = 7'b01_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeBranch  = 7'b11_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeJalr    = 7'b11_001_11;
  localparam [`OPCODE_SIZE:0] OpcodeJal     = 7'b11_011_11;
  localparam [`OPCODE_SIZE:0] OpcodeRegImm  = 7'b00_100_11;
  localparam [`OPCODE_SIZE:0] OpcodeRegReg  = 7'b01_100_11;
  localparam [`OPCODE_SIZE:0] OpcodeEnviron = 7'b11_100_11;
  localparam [`OPCODE_SIZE:0] OpcodeAuipc   = 7'b00_101_11;
  localparam [`OPCODE_SIZE:0] OpcodeLui     = 7'b01_101_11;

  reg [`REG_SIZE:0] cycles_current;
  always @(posedge clk or posedge rst) begin
    if (rst) cycles_current <= 0;
    else cycles_current <= cycles_current + 1;
  end

  // F -> D
  reg [`REG_SIZE:0]  d_pc;
  reg [`INST_SIZE:0] d_inst;
  reg                d_valid;

  // D -> X
  reg [`REG_SIZE:0]  x_pc;
  reg [`INST_SIZE:0] x_inst;
  reg                x_valid;
  reg [4:0]          x_rs1_idx, x_rs2_idx, x_rd_idx;
  reg [`REG_SIZE:0]  x_rs1_val_base, x_rs2_val_base;
  reg                x_is_branch, x_is_jal, x_is_jalr;
  reg                x_is_lui, x_is_auipc, x_is_load, x_is_store;
  reg                x_is_regimm, x_is_regreg, x_is_ecall;
  reg [2:0]          x_funct3;
  reg [6:0]          x_funct7;
  reg [`REG_SIZE:0]  x_imm_i_sext, x_imm_s_sext, x_imm_b_sext, x_imm_j_sext;
  reg [4:0]          x_imm_shamt;

  reg [4:0]          div_p_rd      [0:7];
  reg                div_p_valid   [0:7];
  reg                div_p_rem     [0:7];
  reg                div_p_regwrite[0:7];
  reg                div_p_quot_inv[0:7];
  reg                div_p_rem_inv [0:7];
  reg [`REG_SIZE:0]  div_p_pc      [0:7];
  reg [`INST_SIZE:0] div_p_inst    [0:7];

  // X -> M
  reg [`REG_SIZE:0]  m_pc;
  reg [`INST_SIZE:0] m_inst;
  reg                m_valid;
  reg [4:0]          m_rd_idx;
  reg                m_regwrite, m_memread, m_memwrite;
  reg [3:0]          m_mem_we;
  reg [`REG_SIZE:0]  m_alu_result, m_store_data, m_result;

  // M -> W
  reg [`REG_SIZE:0]  w_pc;
  reg [`INST_SIZE:0] w_inst;
  reg                w_valid;
  reg [4:0]          w_rd_idx_r;
  reg                w_regwrite_r, w_memread;
  reg [`REG_SIZE:0]  w_alu_result;
  reg [2:0]          w_funct3;
  reg [`REG_SIZE:0]  w_result;
  reg [`REG_SIZE:0]  w_load_data_r;

  // --- Forward Declarations ---
  wire [`REG_SIZE:0] div_q_u_final, div_r_u_final;
  reg x_branch_taken;
  
  // --- DIVIDER LOGIC DETECTION ---
  wire x_is_div  = x_is_regreg && (x_funct7 == 7'd1) && (x_funct3 == 3'b100);
  wire x_is_divu = x_is_regreg && (x_funct7 == 7'd1) && (x_funct3 == 3'b101);
  wire x_is_rem  = x_is_regreg && (x_funct7 == 7'd1) && (x_funct3 == 3'b110);
  wire x_is_remu = x_is_regreg && (x_funct7 == 7'd1) && (x_funct3 == 3'b111);
  wire x_is_div_instr = x_is_div || x_is_divu || x_is_rem || x_is_remu;

  // --- HAZARD CONTROL LOGIC ---
  
  // 1. Load-Use Hazard
  wire x_load_use_hazard = x_valid && x_is_load && (x_rd_idx != 0) && d_valid && ((x_rd_idx == d_rs1_idx) || (x_rd_idx == d_rs2_idx));
  wire stall_load = x_load_use_hazard;
  
  // 2. Divider Data Hazard [UPDATED WITH YOUR FRIEND'S LOGIC]
  reg stall_div_data;
  integer h;
    always @(*) begin
        stall_div_data = 1'b0;
        if (d_valid) begin
            for (h = 0; h < `DIVIDER_STAGES-2; h = h + 1) begin
                if (div_p_valid[h] && div_p_regwrite[h] && (div_p_rd[h] != 0)) begin
                    if ((div_p_rd[h] == d_rs1_idx) || (div_p_rd[h] == d_rs2_idx)) begin
                        stall_div_data = 1'b1;
                    end
                end
            end
            if (x_valid && x_is_div_instr && (x_rd_idx != 0)) begin
                if ((x_rd_idx == d_rs1_idx) || (x_rd_idx == d_rs2_idx)) begin
                    stall_div_data = 1'b1;
                end
            end
            
        end
    end

  wire div_result_ready = div_p_valid[7];
  wire struct_hazard_div_wb = div_result_ready && m_valid && m_regwrite;

  integer dh;
  reg div_busy_before_wb;

  always @(*) begin
    div_busy_before_wb = 1'b0;
    for (dh = 0; dh < `DIVIDER_STAGES -3; dh = dh + 1) begin
      if (div_p_valid[dh] && div_p_regwrite[dh] && (div_p_rd[dh] != 5'd0))
        div_busy_before_wb = 1'b1;
    end
    if (x_valid && x_is_div_instr && (x_rd_idx != 5'd0))
      div_busy_before_wb = 1'b1;
  end

    // --- DIV writeback latch for forwarding ---
  reg               div_w_valid;
  reg [4:0]         div_w_rd;
  reg [`REG_SIZE:0] div_w_data;

  wire stall_div_indep = d_valid && !d_is_div_instr && !stall_div_data && div_busy_before_wb;

  wire stall_wb  = stall_load || stall_div_data || stall_div_indep || struct_hazard_div_wb;

  // Enable PC và F->D
  wire pc_en = !stall_wb ;
  wire fd_en = !stall_wb ;

  // X->M 
  wire dx_en = !struct_hazard_div_wb;
  wire xm_en = !struct_hazard_div_wb;

wire dx_clear =
    stall_load ||
    stall_div_data ||
    stall_div_indep || 
    (x_valid && (x_is_jal || x_is_jalr || (x_is_branch && x_branch_taken)));

  // --- FETCH STAGE ---
  reg  [`REG_SIZE:0] f_pc;
  wire [`INST_SIZE:0] f_inst;
  reg                redirect_pc;
  reg  [`REG_SIZE:0]  redirect_pc_target;

  always @(posedge clk or posedge rst) begin
    if (rst) f_pc <= 32'd0;
    else if (pc_en) begin
      if (redirect_pc) f_pc <= redirect_pc_target;
      else f_pc <= f_pc + 4;
    end
  end

  assign pc_to_imem = f_pc;
  assign f_inst     = inst_from_imem;

  // --- F -> D REGISTER ---
  reg flush_fd; 
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      d_pc <= 0; d_inst <= 0; d_valid <= 0;
    end else if (flush_fd) begin
      d_pc <= 0; d_inst <= 0; d_valid <= 0;
    end else if (fd_en) begin
      d_pc <= f_pc; d_inst <= f_inst; d_valid <= 1'b1;
    end
  end

  // --- DECODE STAGE ---
  wire [4:0]         w_rd_idx;
  wire               w_regwrite;
  wire [`REG_SIZE:0] w_wdata;

  wire [6:0] d_funct7;
  wire [4:0] d_rs2_idx, d_rs1_idx, d_rd_idx;
  wire [2:0] d_funct3;
  wire [`OPCODE_SIZE:0] d_opcode;
  assign {d_funct7, d_rs2_idx, d_rs1_idx, d_funct3, d_rd_idx, d_opcode} = d_inst;

  wire [11:0] d_imm_i = d_inst[31:20];
  wire [4:0]  d_imm_shamt = d_inst[24:20];
  wire [11:0] d_imm_s = {d_funct7, d_rd_idx};
  wire [12:0] d_imm_b; assign {d_imm_b[12], d_imm_b[10:1], d_imm_b[11], d_imm_b[0]} = {d_funct7, d_rd_idx, 1'b0};
  wire [20:0] d_imm_j; assign {d_imm_j[20], d_imm_j[10:1], d_imm_j[11], d_imm_j[19:12], d_imm_j[0]} = {d_inst[31:12], 1'b0};

  wire [`REG_SIZE:0] d_imm_i_sext = {{20{d_imm_i[11]}}, d_imm_i[11:0]};
  wire [`REG_SIZE:0] d_imm_s_sext = {{20{d_imm_s[11]}}, d_imm_s[11:0]};
  wire [`REG_SIZE:0] d_imm_b_sext = {{19{d_imm_b[12]}}, d_imm_b[12:0]};
  wire [`REG_SIZE:0] d_imm_j_sext = {{11{d_imm_j[20]}}, d_imm_j[20:0]};

  wire d_is_branch = (d_opcode == OpcodeBranch);
  wire d_is_jal    = (d_opcode == OpcodeJal);
  wire d_is_jalr   = (d_opcode == OpcodeJalr);
  wire d_is_lui    = (d_opcode == OpcodeLui);
  wire d_is_auipc  = (d_opcode == OpcodeAuipc);
  wire d_is_load   = (d_opcode == OpcodeLoad);
  wire d_is_store  = (d_opcode == OpcodeStore);
  wire d_is_regimm = (d_opcode == OpcodeRegImm);
  wire d_is_regreg = (d_opcode == OpcodeRegReg);
  wire d_is_ecall  = (d_opcode == OpcodeEnviron) & (d_inst[31:7] == 0);

    // Detect DIV/REM ở Decode
  wire d_is_div  = d_is_regreg && (d_funct7 == 7'd1) && (d_funct3 == 3'b100);
  wire d_is_divu = d_is_regreg && (d_funct7 == 7'd1) && (d_funct3 == 3'b101);
  wire d_is_rem  = d_is_regreg && (d_funct7 == 7'd1) && (d_funct3 == 3'b110);
  wire d_is_remu = d_is_regreg && (d_funct7 == 7'd1) && (d_funct3 == 3'b111);
  wire d_is_div_instr = d_is_div || d_is_divu || d_is_rem || d_is_remu;


  wire [`REG_SIZE:0] d_rs1_val, d_rs2_val;
  RegFile rf (
    .rd      (w_rd_idx),
    .rd_data (w_wdata),
    .rs1     (d_rs1_idx),
    .rs1_data(d_rs1_val),
    .rs2     (d_rs2_idx),
    .rs2_data(d_rs2_val),
    .clk     (clk),
    .we      (w_regwrite & w_valid),
    .rst     (rst)
  );

  // --- D -> X REGISTER ---
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      x_pc <= 0; x_inst <= 0; x_valid <= 0;
      x_rs1_idx <= 0; x_rs2_idx <= 0; x_rd_idx <= 0;
      x_rs1_val_base <= 0; x_rs2_val_base <= 0;
      x_is_branch <= 0; x_is_jal <= 0; x_is_jalr <= 0;
      x_is_lui <= 0; x_is_auipc <= 0; x_is_load <= 0; x_is_store <= 0;
      x_is_regimm <= 0; x_is_regreg <= 0; x_is_ecall <= 0;
      x_funct3 <= 0; x_funct7 <= 0;
      x_imm_i_sext <= 0; x_imm_s_sext <= 0; x_imm_b_sext <= 0; x_imm_j_sext <= 0; x_imm_shamt <= 0;
    end 
    else if (dx_en) begin 
      if (dx_clear) begin // Insert Bubble
        x_pc <= 0; x_inst <= 0; x_valid <= 0;
        x_rs1_idx <= 0; x_rs2_idx <= 0; x_rd_idx <= 0;
        x_is_branch <= 0; x_is_jal <= 0; x_is_jalr <= 0; x_is_load <= 0; x_is_store <= 0;
        x_is_regimm <= 0; x_is_regreg <= 0; x_is_ecall <= 0;
      end else begin // Normal Update
        x_pc <= d_pc; x_inst <= d_inst; x_valid <= d_valid;
        x_rs1_idx <= d_rs1_idx; x_rs2_idx <= d_rs2_idx; x_rd_idx <= d_rd_idx;
        x_rs1_val_base <= d_rs1_val; 
        x_rs2_val_base <= d_rs2_val;
        
        x_is_branch <= d_is_branch; x_is_jal <= d_is_jal; x_is_jalr <= d_is_jalr;
        x_is_lui <= d_is_lui; x_is_auipc <= d_is_auipc;
        x_is_load <= d_is_load; x_is_store <= d_is_store;
        x_is_regimm <= d_is_regimm; x_is_regreg <= d_is_regreg; x_is_ecall <= d_is_ecall;
        x_funct3 <= d_funct3; x_funct7 <= d_funct7;
        x_imm_i_sext <= d_imm_i_sext; x_imm_s_sext <= d_imm_s_sext;
        x_imm_b_sext <= d_imm_b_sext; x_imm_j_sext <= d_imm_j_sext; x_imm_shamt <= d_imm_shamt;
      end
    end
  end

  // --- EXECUTE STAGE ---
  reg [`REG_SIZE:0] x_rs1_val, x_rs2_val;
  wire [`REG_SIZE:0] div_result_stage7 = div_p_rem[7] ? div_r_u_final : div_q_u_final;
  
always @(*) begin
    x_rs1_val = x_rs1_val_base;

    if (m_valid && m_regwrite && (m_rd_idx != 0) && (m_rd_idx == x_rs1_idx)) begin
        x_rs1_val = m_alu_result; // Lấy kết quả tính toán từ M
    end
    else if (div_p_valid[7] && div_p_regwrite[7] && (div_p_rd[7] != 0) && (div_p_rd[7] == x_rs1_idx)) begin
        x_rs1_val = div_result_stage7;
    end
    else if (w_valid && w_regwrite_r && (w_rd_idx_r != 0) && (w_rd_idx_r == x_rs1_idx)) begin
        x_rs1_val = w_result;
    end
    else if (div_w_valid && (div_w_rd != 5'd0) && (div_w_rd == x_rs1_idx)) begin
        x_rs1_val = div_w_data;
    end
  end

  // --- FORWARDING LOGIC (RS2) ---
  always @(*) begin
    x_rs2_val = x_rs2_val_base;

    if (m_valid && m_regwrite && (m_rd_idx != 0) && (m_rd_idx == x_rs2_idx)) begin
        x_rs2_val = m_alu_result;
    end
    else if (div_p_valid[7] && div_p_regwrite[7] && (div_p_rd[7] != 0) && (div_p_rd[7] == x_rs2_idx)) begin
        x_rs2_val = div_result_stage7;
    end
    else if (w_valid && w_regwrite_r && (w_rd_idx_r != 0) && (w_rd_idx_r == x_rs2_idx)) begin
        x_rs2_val = w_result;
    end
    else if (div_w_valid && (div_w_rd != 5'd0) && (div_w_rd == x_rs2_idx)) begin
        x_rs2_val = div_w_data;
    end
  end

  reg  [`REG_SIZE:0] alu_a, alu_b;
  reg                alu_cin;
  wire [`REG_SIZE:0] alu_sum;
  cla alu_addsub (.a(alu_a), .b(alu_b), .cin(alu_cin), .sum(alu_sum));

  reg  [`REG_SIZE:0] div_a, div_b;
  wire [`REG_SIZE:0] div_q_u, div_r_u;
  DividerUnsignedPipelined u_divu (.clk(clk), .rst(rst), .stall(1'b0), .i_dividend(div_a), .i_divisor(div_b), .o_remainder(div_r_u), .o_quotient(div_q_u));

  wire rs1_sign = x_rs1_val[31];
  wire rs2_sign = x_rs2_val[31];
  wire [`REG_SIZE:0] rs1_abs = rs1_sign ? (~x_rs1_val + 1) : x_rs1_val;
  wire [`REG_SIZE:0] rs2_abs = rs2_sign ? (~x_rs2_val + 1) : x_rs2_val;

  wire div_start = x_valid && x_is_div_instr && !struct_hazard_div_wb;

  integer k;
  always @(posedge clk or posedge rst) begin
      if (rst) begin
          for(k=0; k<7; k=k+1) begin
            div_p_valid[k]    <= 0;
            div_p_rd[k]       <= 0;
            div_p_rem[k]      <= 0;
            div_p_regwrite[k] <= 0;
            div_p_quot_inv[k] <= 0;
            div_p_rem_inv[k]  <= 0;
            div_p_pc[k]       <= 0;
            div_p_inst[k]     <= 0;
          end
      end else begin
          for(k=7; k>0; k=k-1) begin
              div_p_valid[k] <= div_p_valid[k-1];
              div_p_rd[k] <= div_p_rd[k-1];
              div_p_rem[k] <= div_p_rem[k-1];
              div_p_regwrite[k] <= div_p_regwrite[k-1];
              div_p_quot_inv[k] <= div_p_quot_inv[k-1];
              div_p_rem_inv[k] <= div_p_rem_inv[k-1];
              div_p_pc[k] <= div_p_pc[k-1];
              div_p_inst[k] <= div_p_inst[k-1];
          end
          if (div_start) begin
              div_p_valid[0] <= 1;
              div_p_rd[0] <= x_rd_idx;
              div_p_rem[0] <= (x_is_rem || x_is_remu);
              div_p_regwrite[0] <= 1;
              div_p_quot_inv[0] <= (x_is_div || x_is_rem) ? ((x_rs2_val == 0) ? 0 : (rs1_sign ^ rs2_sign)) : 0;
              div_p_rem_inv[0]  <= (x_is_div || x_is_rem) ? rs1_sign : 0;
              div_p_pc[0] <= x_pc;
              div_p_inst[0] <= x_inst;
          end else begin
              div_p_valid[0] <= 0; div_p_rd[0] <= 0; div_p_rem[0] <= 0;
              div_p_regwrite[0] <= 0; div_p_quot_inv[0] <= 0; div_p_rem_inv[0] <= 0;
              div_p_pc[0] <= 0; div_p_inst[0] <= 0;
          end
      end
  end
  
  assign div_q_u_final = div_p_quot_inv[7] ? (~div_q_u + 32'd1) : div_q_u;
  assign div_r_u_final = div_p_rem_inv[7]  ? (~div_r_u + 32'd1) : div_r_u;

  // ALU Control
  reg [`REG_SIZE:0] x_alu_result;
  reg [`REG_SIZE:0] x_branch_target;
  reg               x_regwrite;
  reg               x_memread;
  reg               x_memwrite;
  reg [3:0]         x_mem_we;
  reg [`REG_SIZE:0] x_store_data;
  
  always @(*) begin
    x_alu_result = 0; x_branch_taken = 0; x_branch_target = 0;
    x_regwrite = 0; x_memread = 0; x_memwrite = 0; x_mem_we = 0; x_store_data = 0;
    alu_a = 0; alu_b = 0; alu_cin = 0;
    div_a = 0; div_b = 1;

    if (x_valid) begin
      // LUI
      if (x_is_lui) begin x_alu_result = {x_inst[31:12], 12'd0}; x_regwrite = 1; end
      // AUIPC
      else if (x_is_auipc) begin x_alu_result = x_pc + {x_inst[31:12], 12'd0}; x_regwrite = 1; end
      // JAL
      else if (x_is_jal) begin x_alu_result = x_pc + 4; x_regwrite = 1; x_branch_taken = 1; x_branch_target = x_pc + x_imm_j_sext; end
      // JALR
      else if (x_is_jalr) begin x_alu_result = x_pc + 4; x_regwrite = 1; x_branch_taken = 1; x_branch_target = (x_rs1_val + x_imm_i_sext) & ~1; end
      // BRANCH
      else if (x_is_branch) begin
        if (x_funct3 == 3'b000)      x_branch_taken = (x_rs1_val == x_rs2_val);
        else if (x_funct3 == 3'b001) x_branch_taken = (x_rs1_val != x_rs2_val);
        else if (x_funct3 == 3'b100) x_branch_taken = ($signed(x_rs1_val) < $signed(x_rs2_val));
        else if (x_funct3 == 3'b101) x_branch_taken = ($signed(x_rs1_val) >= $signed(x_rs2_val));
        else if (x_funct3 == 3'b110) x_branch_taken = (x_rs1_val < x_rs2_val);
        else if (x_funct3 == 3'b111) x_branch_taken = (x_rs1_val >= x_rs2_val);
        else                         x_branch_taken = 1'b0;

        if (x_branch_taken) x_branch_target = x_pc + x_imm_b_sext;
      end
      // LOAD
      else if (x_is_load) begin
        x_memread = 1; x_regwrite = 1;
        alu_a = x_rs1_val; alu_b = x_imm_i_sext; alu_cin = 0; x_alu_result = alu_sum;
      end
      // STORE 
      else if (x_is_store) begin
        x_memwrite = 1;
        alu_a = x_rs1_val; alu_b = x_imm_s_sext; alu_cin = 0; x_alu_result = alu_sum;
        
        x_store_data = x_rs2_val << (x_alu_result[1:0] * 8);
        
        if (x_funct3 == 3'b000)      x_mem_we = 4'b0001 << x_alu_result[1:0]; // SB
        else if (x_funct3 == 3'b001) x_mem_we = 4'b0011 << (x_alu_result[1] * 2); // SH
        else if (x_funct3 == 3'b010) x_mem_we = 4'b1111; // SW
        else                         x_mem_we = 4'b0000;
      end
      // REG-IMM
      else if (x_is_regimm) begin
        x_regwrite = 1;
        if (x_funct3 == 3'b000) begin // ADDI
          alu_a = x_rs1_val; alu_b = x_imm_i_sext; alu_cin = 0; x_alu_result = alu_sum;
        end
        else if (x_funct3 == 3'b010) x_alu_result = ($signed(x_rs1_val) < $signed(x_imm_i_sext)) ? 1 : 0;
        else if (x_funct3 == 3'b011) x_alu_result = (x_rs1_val < x_imm_i_sext) ? 1 : 0;
        else if (x_funct3 == 3'b100) x_alu_result = x_rs1_val ^ x_imm_i_sext;
        else if (x_funct3 == 3'b110) x_alu_result = x_rs1_val | x_imm_i_sext;
        else if (x_funct3 == 3'b111) x_alu_result = x_rs1_val & x_imm_i_sext;
        else if (x_funct3 == 3'b001) x_alu_result = x_rs1_val << x_imm_shamt;
        else if (x_funct3 == 3'b101) begin
          if (x_funct7[5]) x_alu_result = $signed(x_rs1_val) >>> x_imm_shamt;
          else x_alu_result = x_rs1_val >> x_imm_shamt;
        end
      end
      // REG-REG
      else if (x_is_regreg) begin
        x_regwrite = 1;
        if (x_funct7 == 0 && x_funct3 == 0) begin // ADD
          alu_a = x_rs1_val; alu_b = x_rs2_val; alu_cin = 0; x_alu_result = alu_sum;
        end
        else if (x_funct7 == 7'b0100000 && x_funct3 == 0) begin // SUB
          alu_a = x_rs1_val; alu_b = ~x_rs2_val; alu_cin = 1; x_alu_result = alu_sum;
        end
        else if (x_funct7 == 0 && x_funct3 == 3'b001) x_alu_result = x_rs1_val << x_rs2_val[4:0];
        else if (x_funct7 == 0 && x_funct3 == 3'b010) x_alu_result = ($signed(x_rs1_val) < $signed(x_rs2_val)) ? 1 : 0;
        else if (x_funct7 == 0 && x_funct3 == 3'b011) x_alu_result = (x_rs1_val < x_rs2_val) ? 1 : 0;
        else if (x_funct7 == 0 && x_funct3 == 3'b100) x_alu_result = x_rs1_val ^ x_rs2_val;
        else if (x_funct7 == 0 && x_funct3 == 3'b101) x_alu_result = x_rs1_val >> x_rs2_val[4:0];
        else if (x_funct7 == 7'b0100000 && x_funct3 == 3'b101) x_alu_result = $signed(x_rs1_val) >>> x_rs2_val[4:0];
        else if (x_funct7 == 0 && x_funct3 == 3'b110) x_alu_result = x_rs1_val | x_rs2_val;
        else if (x_funct7 == 0 && x_funct3 == 3'b111) x_alu_result = x_rs1_val & x_rs2_val;
        // M-Extension
        else if (x_funct7 == 1 && x_funct3 == 3'b000) x_alu_result = x_rs1_val * x_rs2_val;
        else if (x_funct7 == 1 && x_funct3 == 3'b001) x_alu_result = ($signed({{32{x_rs1_val[31]}}, x_rs1_val}) * $signed({{32{x_rs2_val[31]}}, x_rs2_val})) >> 32;
        else if (x_funct7 == 1 && x_funct3 == 3'b010) x_alu_result = ($signed({{32{x_rs1_val[31]}}, x_rs1_val}) * {32'd0, x_rs2_val}) >> 32;
        else if (x_funct7 == 1 && x_funct3 == 3'b011) x_alu_result = ({32'd0, x_rs1_val} * {32'd0, x_rs2_val}) >> 32;
        // DIV Inputs
        else if (x_funct7 == 1 && (x_funct3 == 3'b100 || x_funct3 == 3'b110)) begin div_a = rs1_abs; div_b = rs2_abs; end
        else if (x_funct7 == 1 && (x_funct3 == 3'b101 || x_funct3 == 3'b111)) begin div_a = x_rs1_val; div_b = x_rs2_val; end
      end
    end
  end

  // Redirect/Flush Logic
  always @(*) begin
    redirect_pc = 0; redirect_pc_target = 0; flush_fd = 0;
    if (x_valid) begin
      if (x_is_jal || x_is_jalr || (x_is_branch && x_branch_taken)) begin
        redirect_pc = 1; redirect_pc_target = x_branch_target; flush_fd = 1;
      end
    end
  end

  // --- X -> M REGISTER ---
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      m_pc <= 0; m_inst <= 0; m_valid <= 0;
      m_rd_idx <= 0; m_regwrite <= 0; m_memread <= 0; m_memwrite <= 0;
      m_mem_we <= 0; m_alu_result <= 0; m_store_data <= 0;
    end
    else if (xm_en) begin
      // If DIV instruction, send BUBBLE to M.
      if (x_valid && x_is_div_instr) begin
        m_pc <= x_pc; m_inst <= x_inst; 
        m_valid <= 0; // BUBBLE
        m_regwrite <= 0; m_memread <= 0; m_memwrite <= 0; m_mem_we <= 0;
      end else begin
        m_pc <= x_pc; m_inst <= x_inst; m_valid <= x_valid;
        m_rd_idx <= x_rd_idx; m_regwrite <= x_regwrite;
        m_memread <= x_memread; m_memwrite <= x_memwrite; m_mem_we <= x_mem_we;
        m_alu_result <= x_alu_result; m_store_data <= x_store_data;
      end
    end
  end

  // --- MEMORY STAGE ---
  always @(*) begin
    addr_to_dmem = m_alu_result;
    store_we_to_dmem = 0; store_data_to_dmem = 0; m_result = m_alu_result;
    if (m_valid) begin
      if (m_memwrite) begin
        store_we_to_dmem = m_mem_we;
        store_data_to_dmem = m_store_data;
      end
    end
  end

  // --- M -> W REGISTER ---
  assign w_rd_idx = w_rd_idx_r;
  assign w_regwrite = w_regwrite_r;

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      w_pc <= 0; w_inst <= 0; w_valid <= 0;
      w_rd_idx_r <= 0; w_regwrite_r <= 0; w_memread <= 0;
      w_alu_result <= 0; w_funct3 <= 0;
      w_load_data_r <= 0;

            // reset latch DIV
      div_w_valid <= 1'b0;
      div_w_rd    <= 5'd0;
      div_w_data  <= {(`REG_SIZE+1){1'b0}};
    end
    // Priority: Divider Finish -> Writeback
    else if (div_result_ready) begin
      w_valid <= 1;
      w_regwrite_r <= div_p_regwrite[7];
      w_rd_idx_r <= div_p_rd[7];
      w_alu_result <= div_p_rem[7] ? div_r_u_final : div_q_u_final;
      w_memread <= 0;
      w_pc <= div_p_pc[7];
      w_inst <= div_p_inst[7];
      w_funct3 <= 0;
      w_load_data_r <= 0;

      div_w_valid <= div_p_regwrite[7];
      div_w_rd    <= div_p_rd[7];
      div_w_data  <= div_p_rem[7] ? div_r_u_final : div_q_u_final;
    end
    else if (struct_hazard_div_wb) begin
    end
    else begin
      w_pc        <= m_pc;
      w_inst      <= m_inst;
      w_valid     <= m_valid;
      w_rd_idx_r  <= m_rd_idx;
      w_regwrite_r<= m_regwrite;
      w_memread   <= m_memread;
      w_alu_result<= m_alu_result;
      w_funct3    <= m_inst[14:12];
      w_load_data_r <= load_data_from_dmem;
      if (div_w_valid && w_valid && w_regwrite_r && (w_rd_idx_r == div_w_rd))
        div_w_valid <= 1'b0;
    end
  end

  // --- WRITEBACK STAGE ---
  wire [`REG_SIZE:0] w_load_data = w_load_data_r;
  always @(*) begin
    w_result = w_alu_result;
    if (w_memread) begin
      if (w_funct3 == 3'b000) begin // LB
          if (w_alu_result[1:0] == 2'b00)      w_result = {{24{w_load_data[7]}}, w_load_data[7:0]};
          else if (w_alu_result[1:0] == 2'b01) w_result = {{24{w_load_data[15]}}, w_load_data[15:8]};
          else if (w_alu_result[1:0] == 2'b10) w_result = {{24{w_load_data[23]}}, w_load_data[23:16]};
          else                                 w_result = {{24{w_load_data[31]}}, w_load_data[31:24]};
      end
      else if (w_funct3 == 3'b001) begin // LH
          if (w_alu_result[1]) w_result = {{16{w_load_data[31]}}, w_load_data[31:16]};
          else                 w_result = {{16{w_load_data[15]}}, w_load_data[15:0]};
      end
      else if (w_funct3 == 3'b010) begin // LW
          w_result = w_load_data;
      end
      else if (w_funct3 == 3'b100) begin // LBU
          if (w_alu_result[1:0] == 2'b00)      w_result = {24'd0, w_load_data[7:0]};
          else if (w_alu_result[1:0] == 2'b01) w_result = {24'd0, w_load_data[15:8]};
          else if (w_alu_result[1:0] == 2'b10) w_result = {24'd0, w_load_data[23:16]};
          else                                 w_result = {24'd0, w_load_data[31:24]};
      end
      else if (w_funct3 == 3'b101) begin // LHU
          if (w_alu_result[1]) w_result = {16'd0, w_load_data[31:16]};
          else                 w_result = {16'd0, w_load_data[15:0]};
      end
      else begin
          w_result = w_load_data;
      end
    end
  end

  assign w_wdata = w_result;

  always @(posedge clk or posedge rst) begin
    if (rst) halt <= 0;
    else if (w_valid && (w_inst[6:0] == OpcodeEnviron) && (w_inst[31:7] == 0)) halt <= 1;
  end

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      trace_writeback_pc <= 0; trace_writeback_inst <= 0;
    end else begin
      if (w_valid) begin
        trace_writeback_pc <= w_pc;
        trace_writeback_inst <= w_inst;
      end else begin
        trace_writeback_pc <= 0; trace_writeback_inst <= 0;
      end
    end
  end

endmodule

module MemorySingleCycle #(
    parameter NUM_WORDS = 512
) (
    input                    rst,
    input                    clk,
    input      [`REG_SIZE:0] pc_to_imem,
    output reg [`REG_SIZE:0] inst_from_imem,
    input      [`REG_SIZE:0] addr_to_dmem,
    output reg [`REG_SIZE:0] load_data_from_dmem,
    input      [`REG_SIZE:0] store_data_to_dmem,
    input      [         3:0] store_we_to_dmem
);

  reg [`REG_SIZE:0] mem_array[0:NUM_WORDS-1];

  initial begin
    $readmemh("D:/SOC_Lab/assignment/test/mem_initial_contents.hex", mem_array);
  end

  localparam AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam AddrLsb = 2;

  always @(negedge clk) begin
    inst_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
  end

  always @(negedge clk) begin
    if (store_we_to_dmem[0]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
    end
    if (store_we_to_dmem[1]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
    end
    if (store_we_to_dmem[2]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
    end
    if (store_we_to_dmem[3]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
    end
    load_data_from_dmem <= mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];
  end
endmodule

module Processor (
    input                 clk,
    input                 rst,
    output                halt,
    output [ `REG_SIZE:0] trace_writeback_pc,
    output [`INST_SIZE:0] trace_writeback_inst
);

  wire [`INST_SIZE:0] inst_from_imem;
  wire [ `REG_SIZE:0] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [         3:0] mem_data_we;

  wire [(8*32)-1:0] test_case;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) memory (
    .rst                 (rst),
    .clk                 (clk),
    .pc_to_imem          (pc_to_imem),
    .inst_from_imem      (inst_from_imem),
    .addr_to_dmem        (mem_data_addr),
    .load_data_from_dmem (mem_data_loaded_value),
    .store_data_to_dmem  (mem_data_to_write),
    .store_we_to_dmem    (mem_data_we)
  );

  DatapathPipelined datapath (
    .clk                  (clk),
    .rst                  (rst),
    .pc_to_imem           (pc_to_imem),
    .inst_from_imem       (inst_from_imem),
    .addr_to_dmem         (mem_data_addr),
    .store_data_to_dmem   (mem_data_to_write),
    .store_we_to_dmem     (mem_data_we),
    .load_data_from_dmem  (mem_data_loaded_value),
    .halt                 (halt),
    .trace_writeback_pc   (trace_writeback_pc),
    .trace_writeback_inst (trace_writeback_inst)
  );

endmodule
