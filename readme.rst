8-bit RISC Verilog implementation of CPU
========================


1. Design requirements
------------

The basic structure of the vast majority of computers today, whether they are mainframes or microcomputers, is the Von Neumann architecture, that is, the computer consists of five parts: controller, arithmetic unit, memory, and input/output devices. Both instructions and programs are stored in memory.

|image0|

The central processing unit, also known as the microprocessor , is the core of the computer system. Mainly complete the following tasks: (1) Fetch instructions from memory and decode instructions; (2) Perform simple arithmetic and logic operations; (3) Transfer data between processor and memory or I/O; (4) Program flow direction control etc. [1].

RISC, reduced instruction set
computer, reduced instruction set computer compared to CISC, complex instruction set
Computer, a complex instruction set computer can execute more instructions in one cycle. These instructions are shorter, simpler in function, and more uniform in instruction format than CISC instruction sets, so they are suitable for pipeline processing and speed up processing.

The 8-bit CPU is a typical CPU structure adopted in the 1970s, and the representative products include Intel's 8080 series [1]. It is the beginning of the 64-bit and 32-bit bus structure CPU commonly used in modern times.

This paper will be based on the finite state machine (FSM) adopts Verilog hardware description language to implement 8-bit RISC architecture CPU.

2. Hardware composition
------------

|image1|

As shown in the figure, it is a key component of a microcomputer system, including CPU, memory, data and address buses. CPU is mainly composed of arithmetic logic unit (ALU), accumulator, general registers, program counter (PC), instruction register (IR), address multiplexer. The memory here refers to the main memory, which is divided into random access memory RAM and read-only memory ROM. The main memory and the CPU are accessed through the bus. The bus has two types: address bus (Address Bus) and data bus (Data Address).

2.1 Memory
~~~~~~~~~~

2.1.1 ROM
^^^^^^^^^

ROM is used to store the instructions to be executed, see Chapter 3 for the introduction of instructions.

Verilog implementation ：

.. code:: verilog

   module rom(data, addr, read, ena);
   input read, ena;
   input [7:0] addr;
   output [7:0] data;
    
   reg [7:0] memory[255:0];


   // note: Decimal number in the bracket
   initial begin
       memory[0] = 8'b000_00000;   //NOP
       ... // some instructions
   end

   assign data = (read&&ena)? memory[addr]:8'hzz;  

   endmodule

ROM, read-only instructions. Accept the input address, when the read signal and enable signal are high level, output the instruction corresponding to the address storage, otherwise the output remains in a high-impedance state. Both address and data are 8 bits, addressable and the size of internal storage is 256Bytes。

|image2|

RTL (register-transfer level) synthesis is shown in the figure above.

2.2.2 RAM
^^^^^^^^^

Store data, readable and writable.

Verilog implementation:

.. code:: verilog

   module ram(data, addr, ena, read, write);
   input ena, read, write;
   input [7:0] addr;
   inout [7:0] data;

   reg [7:0] ram[255:0];

   assign data = (read&&ena)? ram[addr]:8'hzz;     // read data from RAM

   always @(posedge write) begin   // write data to RAM
       ram[addr] <= data;
   end
   endmodule

Readable and writable, receiving an 8-bit address, when the read signal and enable signal are valid, output the data stored in the corresponding address, otherwise the output remains in a high-impedance state. When the rising edge of the write signal is triggered, the input and output are written to the corresponding position of the address. The internal storage and addressable size are also 256Byters.

|image3|

The RTL view is as above.

2.2 CPU
~~~~~~~

2.2.1 PC
^^^^^^^^

The program counter, sometimes called the instruction address register (IAR), corresponds to the instruction pointer register in the Intel X86 system CPU. Its function is to store the offset address of the next instruction to be executed in the current code segment. In this paper, the PC is automatically modified by the Controller, so that the address of the next instruction to be executed is always stored in it. Therefore, PC is a register used to control the execution flow of instruction sequences [2].

Verilog implementation:

.. code:: verilog

   //PC, program counter
   module counter(pc_addr, clock, rst, en);
   input clock, rst, en;
   output reg [7:0] pc_addr;
   always @(posedge clock or negedge rst) begin
       if(!rst) pc_addr <= 8'd0;
       else begin
           if(en) pc_addr <= pc_addr+1;
           else pc_addr <= pc_addr;
       end
   end
   endmodule

Cleared asynchronously. Triggered by the rising edge of the clock, the program counter counts when the high level is enabled, and points to the address of the next instruction to be executed. Instructions are stored in ROM, so pc_addr is incremented by 1 each time.
|image4|

The RTL view is as above.

2.2.2 Accumulator
^^^^^^^^^^^^

Accumulators are used to store intermediate results of calculations.

Verilog implementation :

.. code:: verilog

   // Accumulator
   module accum( in, out, ena, clk, rst); 
   // a register, to storage result after computing
   input clk,rst,ena;
   input [7:0] in;
   output reg [7:0] out;

   always @(posedge clk or negedge rst) begin  
       if(!rst) out <= 8'd0;
       else begin
           if(ena) out <= in;
           else    out <= out;
       end
   end
   endmodule

Cleared asynchronously. Triggered by the rising edge of the clock, the current input signal is output when the high level is enabled.

|image5|

RTL as shown above, it can be seen that it is realized by a Q flip-flop.

2.2.3 Address Multiplexer
^^^^^^^^^^^^^^^^

Accepting the control enable signal selects the input address from the program counter and instruction register.

Verilog implementation : 

.. code:: verilog

   // Address multiplexer
   module addr_mux(addr, sel, ir_ad, pc_ad); 
   // To choose address of instruction register or address of program counter
   input [7:0] ir_ad, pc_ad;
   input sel;
   output [7:0] addr;
   assign addr = (sel)? ir_ad:pc_ad;
   endmodule

When the select signal is 1, the address from the register input is selected to the data bus, otherwise the address in the program counter is loaded to the data bus.

|image6|

RTL view as above.

2.2.4 ALU
^^^^^^^^^

The arithmetic and logic operation unit determines which operation to perform according to the instruction type, so as to output the operation result to the general-purpose register or the accumulator.

.. code:: verilog

   module alu(alu_out, alu_in, accum, op);
   // Arithmetic logic unit
   // to perform arithmetic and logic operations.
   input [2:0] op;
   input [7:0] alu_in,accum;
   output reg [7:0] alu_out;

   parameter   NOP=3'b000,
               LDO=3'b001,
               LDA=3'b010,
               STO=3'b011,
               PRE=3'b100,
               ADD=3'b101,
               LDM=3'b110,
               HLT=3'b111;

   always @(*) begin
           casez(op)
           NOP:    alu_out = accum;
           HLT:    alu_out = accum;
           LDO:    alu_out = alu_in;
           LDA:    alu_out = alu_in;
           STO:    alu_out = accum;
           PRE:    alu_out = alu_in;
           ADD:    alu_out = accum+alu_in;
           LDM:    alu_out = accum;
           default:    alu_out = 8'bzzzz_zzzz;
           endcase
   end 
   endmodule

|image7|

The RTL view is as above.

2.2.5 General purpose registers
^^^^^^^^^^^^^^^^^

General-purpose registers, ALU output results, and operands output by instruction registers can all be stored at specific addresses in registers. Output the data stored in the register to the data bus.

Verilog implementation:

.. code:: verilog

   module reg_32(in, data, write, read, addr, clk);
   input write, read, clk;
   input [7:0] in;
   input [7:0] addr; 
   //!Warning: addr should be reduced to 5 bits width, not 8 bits width.
   //input [4:0] addr;

   output [7:0] data;

   reg [7:0] R[31:0]; //32Byte
   wire [4:0] r_addr;

   assign r_addr = addr[4:0];
   assign data = (read)? R[r_addr]:8'hzz;  //read enable

   always @(posedge clk) begin             //write, clk posedge
       if(write)   R[r_addr] <= in; 
   end
   endmodule

When the write signal is asserted, the input data (output from the ALU) is stored to a specific address in the register. When the read signal is active, the data at the specified location in the register is output (to the data bus). The register size is 32Bytes.

|image8|

The RTL view is as above.

2.2.6 IR
^^^^^^^^^

Instruction register, which takes data from the data bus, outputs specific instructions and addresses to the ALU, general-purpose registers, and address selectors according to the type of instruction according to the input control signal.

verilog implementation :

.. code:: verilog

   // instruction register
   module ins_reg(data, fetch, clk, rst, ins, ad1, ad2);
   input clk, rst;
   input [1:0] fetch;
   input [7:0] data;
   output [2:0] ins;
   output [4:0] ad1;
   output [7:0] ad2;

   reg [7:0] ins_p1, ins_p2;
   reg [2:0] state;

   assign ins = ins_p1[7:5]; //hign 3 bits, instructions
   assign ad1 = ins_p1[4:0]; //low 5 bits, register address
   assign ad2 = ins_p2;

   always @(posedge clk or negedge rst) begin
       if(!rst) begin
           ins_p1 <= 8'd0;
           ins_p2 <= 8'd0;
       end
       else begin
           if(fetch==2'b01) begin          //fetch==2'b01 operation1, to fetch data from REG
               ins_p1 <= data;
               ins_p2 <= ins_p2;
           end
           else if(fetch==2'b10) begin     //fetch==2'b10 operation2, to fetch data from RAM/ROM
               ins_p1 <= ins_p1;
               ins_p2 <= data;
           end
           else begin
               ins_p1 <= ins_p1;
               ins_p2 <= ins_p2;
           end
       end
   end
   endmodule

Cleared asynchronously. When the input control signal is \ ``01``\, it means that the data bus is currently an instruction (in the form of instruction code + register address, see Chapter 3), and it is changed from \ ``ins``\ and \ ``ad1` `\ Output, when the control signal is \ ``10``\, it means that the data on the current data bus is data (8-bit address data, see Chapter 3), output it from \ ``ad2``\ to the address Selector.

|image9|

The RTL view is as above.

2.3 Internal structure (total)
~~~~~~~~~~~~~~~~~~

|image10|

The figure is a schematic diagram of the internal structure of the system, which shows the connection relationship between various components. The data bus and address bus are the core of the bus system. The address bus connects the output of the address selector, the input of the ROM and the RAM. The address bus is connected to the output of the ROM/RAM, the input of the IR to the ALU, and the output of the general register. The controller (upper left in the figure) is the control unit of the system, see Chapter 4 for details.

The Verilog description of the entire hardware system using component instantiation statements is as follows:

.. code:: verilog

   // Core
   // Top-level entity(except core-tb)
   module core(clk, rst);  
   input clk, rst;

   wire write_r, read_r, PC_en, ac_ena, ram_ena, rom_ena;
   wire ram_write, ram_read, rom_read, ad_sel;

   wire [1:0] fetch;
   wire [7:0] data, addr;
   wire [7:0] accum_out, alu_out;
   wire [7:0] ir_ad, pc_ad;
   wire [4:0] reg_ad;
   wire [2:0] ins;

   ram RAM1(.data(data), 
            .addr(addr), 
            .ena(ram_ena), 
            .read(ram_read), 
            .write(ram_write));  //module ram(data, addr, ena, read, write);

   rom ROM1(.data(data), 
            .addr(addr), 
            .ena(rom_ena), 
            .read(rom_read));    //module rom(data, addr, read, ena);

   addr_mux MUX1(.addr(addr), 
                 .sel(ad_sel), 
                 .ir_ad(ir_ad), 
                 .pc_ad(pc_ad)); //module addr_mux(addr, sel, ir_ad, pc_ad); 

   counter PC1(.pc_addr(pc_ad), 
               .clock(clk), 
               .rst(rst), 
               .en(PC_en));    //module counter(pc_addr, clock, rst, en);

   accum ACCUM1(.out(accum_out), 
                .in(alu_out), 
                .ena(ac_ena), 
                .clk(clk), 
                .rst(rst));        //module accum( in, out, ena, clk, rst); 

   alu ALU1(.alu_out(alu_out), 
            .alu_in(data), 
            .accum(accum_out), 
            .op(ins));             // module alu(alu_out, alu_in, accum, op);

   reg_32 REG1(.in(alu_out), 
               .data(data), 
               .write(write_r), 
               .read(read_r), 
               .addr({ins,reg_ad}), 
               .clk(clk)); 
    //module reg_32(in, data, write, read, addr, clk);
   //reg_32 REG1(.in(alu_out), .data(data), .write(write_r), .read(read_r), .addr(reg_ad), .clk(clk));     
    //module reg_32(in, data, write, read, addr, clk);

   ins_reg IR1(.data(data), 
               .fetch(fetch), 
               .clk(clk), 
               .rst(rst), 
               .ins(ins), 
               .ad1(reg_ad), 
               .ad2(ir_ad));   
   //module ins_reg(data, fetch, clk, rst, ins, ad1, ad2);

   //module machine(ins, clk, rst, write_r, read_r, PC_en, fetch, ac_ena, ram_ena, rom_ena,ram_write, ram_read, rom_read, ad_sel);
   controller CONTROLLER1(.ins(ins), 
                       .clk(clk), 
                       .rst(rst), 
                       .write_r(write_r), 
                       .read_r(read_r), 
                       .PC_en(PC_en), 
                       .fetch(fetch), 
                       .ac_ena(ac_ena), 
                       .ram_ena(ram_ena), 
                       .rom_ena(rom_ena),
                       .ram_write(ram_write), 
                       .ram_read(ram_read), 
                       .rom_read(rom_read), 
                       .ad_sel(ad_sel)
                       );
   endmodule

|image11|

The overall RTL view of the system after instantiation of each module is as above.

3. Instruction set
----------

We define two types of RISC instruction set lengths, namely short instructions and long instructions:

|image12|

|image13|

Among them, the instruction code adopts three-bit binary representation, and there are 8 kinds of instructions defined. The short instruction has 8 bits in total, the upper three bits are the instruction code, and the lower five bits are the address of the general register. The long instruction is 16 bits, and each long instruction is fetched twice, 8 bits are fetched each time, the high 8 bits are fetched first, the format is the same as the short instruction, and the high 3 bits are the instruction code, and the low 5 bits are the general register address; The lower 8 bits are fetched twice to indicate the ROM or RAM address, depending on the instruction code.

Therefore, the instruction set is shown in the following table. In order to facilitate the understanding of the abbreviated meaning of the instruction, the table is described in English and the origin of the abbreviation is expressed in bold:

+---+---+---------------------------------------+---+---------------------+
| I | B | Description                           | T | Comment             |
| N | i |                                       | y |                     |
| S | n |                                       | p |                     |
|   | a |                                       | e |                     |
|   | r |                                       |   |                     |
|   | y |                                       |   |                     |
+===+===+=======================================+===+=====================+
| N | 0 | **N**\ o **op**\ eration              | S | No Operation        |
| O | 0 |                                       | h |                     |
| P | 0 |                                       | o |                     |
|   |   |                                       | r |                     |
|   |   |                                       | t |                     |
+---+---+---------------------------------------+---+---------------------+
| L | 0 | **L**\ oa\ **d**\ s the contents of   | L | REG[reg_addr]<-ROM[ |
| D | 0 | the R\ **O**\ M address into the REG  | o | ROM_addr]           |
| O | 1 | address                               | n |                     |
|   |   |                                       | g |                     |
+---+---+---------------------------------------+---+---------------------+
| L | 0 | **L**\ oa\ **d**\ s the contents of   | L | REG[reg_addr]<-RAM[ |
| D | 1 | the R\ **A**\ M address into the REG  | o | RAM_addr]           |
| A | 0 | address                               | n |                     |
|   |   |                                       | g |                     |
+---+---+---------------------------------------+---+---------------------+
| S | 0 | **Sto**\ re intermediate results into | L | RAM[RAM_addr]<-REG[ |
| T | 1 | RAM address                           | o | reg_addr]           |
| O | 1 |                                       | n |                     |
|   |   |                                       | g |                     |
+---+---+---------------------------------------+---+---------------------+
| P | 1 | **Pre**\ fetch Data from REG address  | S | ACCUM<-REG[reg_addr |
| R | 0 |                                       | h | ]                   |
| E | 0 |                                       | o |                     |
|   |   |                                       | r |                     |
|   |   |                                       | t |                     |
+---+---+---------------------------------------+---+---------------------+
| A | 1 | **Add**\ s the contents of the REG    | S | accumulator<-REG[re |
| D | 0 | address or integer to the accumulator | h | g_addr]+            |
| D | 1 |                                       | o | ACCUM               |
|   |   |                                       | r |                     |
|   |   |                                       | t |                     |
+---+---+---------------------------------------+---+---------------------+
| L | 1 | **Lo**\ ad **M**\ ultiple             | S | REG[reg_addr]<-ACCU |
| D | 1 |                                       | h | M                   |
| M | 0 |                                       | o |                     |
|   |   |                                       | r |                     |
|   |   |                                       | t |                     |
+---+---+---------------------------------------+---+---------------------+
| H | 1 | **H**\ a\ **lt**                      | S | Halt                |
| L | 1 |                                       | h |                     |
| T | 1 |                                       | o |                     |
|   |   |                                       | r |                     |
|   |   |                                       | t |                     |
+---+---+---------------------------------------+---+---------------------+

4. Controller
----------

The controller is the core of the system and has the following functions: fetching instructions, queuing instructions, reading and writing operands, bus control, etc. Here, the (Mealy type) finite state machine (FSM) is used to realize the controller, and the instructions are stored in the ROM for execution. The controller receives the external clock and reset signal, and the controller performs state transfer according to the current state and input.

4.1 State transition diagram
~~~~~~~~~~~~~~

|image14|

According to the task of the instruction, we designed the state transition diagram as shown in the figure above, from left to right are states Sidle, S0~S12. The meaning of each status is as follows:

============ ============== ===================================
Source State Description    Comment
============ ============== ===================================
S0           Load ir1       Fetch instruction 1 (the first short instruction or long instruction)
S1           PC+1           Each execution of a PC+1
S2           HLT            Halt
S3           Load ir2       Fetch instruction 2
S4           PC+1           Each execution of a PC+1
S5           ROM/RAM to REG LDA/LDO
S6           Protect        Write protection
S7           Read REG       STO phase No.1
S8           Write RAM      STO phase No.2
S9           Read REG       PRE/ADD，phase No.1
S10          Write ACCUM    PRE/ADD，phase No.2
S11          Write REG      LDM
S12          Protect        LDM
Sidle        Reset          Reboot
============ ============== ===================================

The transitions between states are:

===== == == == == == == == == == == === === === =====
\     S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 Sidle
===== == == == == == == == == == == === === === =====
S0    1  0  0  0  0  0  0  0  0  0  0   0   0   1
S1    0  1  0  0  0  0  0  0  0  0  0   0   0   1
S2    0  0  1  0  0  0  0  0  0  0  0   0   0   1
S3    0  0  0  1  0  0  0  0  0  0  0   0   0   1
S4    0  0  0  0  1  0  0  0  0  0  0   0   0   1
S5    0  0  0  0  0  1  0  0  0  0  0   0   0   1
S6    0  0  0  0  0  0  1  0  0  0  0   0   0   1
S7    0  0  0  0  0  0  0  1  0  0  0   0   0   1
S8    0  0  0  0  0  0  0  0  1  0  0   0   0   1
S9    0  0  0  0  0  0  0  0  0  1  0   0   0   1
S10   0  0  0  0  0  0  0  0  0  0  1   0   0   1
S11   0  0  0  0  0  0  0  0  0  0  0   1   0   1
S12   0  0  0  0  0  0  0  0  0  0  0   0   1   1
Sidle 0  0  0  0  0  0  0  0  0  0  0   0   0   0
===== == == == == == == == == == == === === === =====

+--------+------------+-----------------------------------------------+
| Source | Destinatio | Condition                                     |
| State  | n          |                                               |
|        | State      |                                               |
+========+============+===============================================+
| S0     | S1         |                                               |
+--------+------------+-----------------------------------------------+
| S1     | S0         | (!ins[0]).(!ins[1]).(!ins[2])                 |
+--------+------------+-----------------------------------------------+
| S1     | S3         | (!ins[0]).(ins[1]).(!ins[2]) +                |
|        |            | (ins[0]).(!ins[2])                            |
+--------+------------+-----------------------------------------------+
| S1     | S11        | (!ins[0]).(ins[1]).(ins[2])                   |
+--------+------------+-----------------------------------------------+
| S1     | S9         | (!ins[1]).(ins[2])                            |
+--------+------------+-----------------------------------------------+
| S1     | S2         | (ins[0]).(ins[1]).(ins[2])                    |
+--------+------------+-----------------------------------------------+
| S2     | S2         |                                               |
+--------+------------+-----------------------------------------------+
| S3     | S4         |                                               |
+--------+------------+-----------------------------------------------+
| S4     | S7         | (!ins[0]).(!ins[1]) +                         |
|        |            | (!ins[0]).(ins[1]).(ins[2]) +                 |
|        |            | (ins[0]).(!ins[1]).(ins[2]) +                 |
|        |            | (ins[0]).(ins[1])                             |
+--------+------------+-----------------------------------------------+
| S4     | S5         | (!ins[0]).(ins[1]).(!ins[2]) +                |
|        |            | (ins[0]).(!ins[1]).(!ins[2])                  |
+--------+------------+-----------------------------------------------+
| S5     | S6         |                                               |
+--------+------------+-----------------------------------------------+
| S6     | S0         |                                               |
+--------+------------+-----------------------------------------------+
| S7     | S8         |                                               |
+--------+------------+-----------------------------------------------+
| S8     | S0         |                                               |
+--------+------------+-----------------------------------------------+
| S9     | S10        |                                               |
+--------+------------+-----------------------------------------------+
| S10    | S0         |                                               |
+--------+------------+-----------------------------------------------+
| S11    | S12        |                                               |
+--------+------------+-----------------------------------------------+
| S12    | S0         |                                               |
+--------+------------+-----------------------------------------------+
| Sidle  | S0         |                                               |
+--------+------------+-----------------------------------------------+

For example, we can see the state transition of S0 and S1:

|image15|

|image16|

Please see the attachment \ ``fsm.pdf``\ for details.

Regarding the verilog implementation of the illustrated finite state machine, a classic 3-segment structure is used here: state register (state
register), the next state combinational logic circuit (Next-state combinational
logic), output combinational logic circuit (Output combinational logic).

4.2 Status Register of FSM
~~~~~~~~~~~~~~~~~~~~

The essence is a D flip-flop, which is responsible for assigning the next state to the current state value (that is, jumping to the next state), and clearing it asynchronously.

.. code:: verilog

   //PART A: D flip latch; State register
   always @(posedge clk or negedge rst) 
   begin
       if(!rst) state<=Sidle;
           //current_state <= Sidle;
       else state<=next_state;
           //current_state <= next_state;  
   end

4.3 Combination logic of a state under FSM
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Responsible for the transfer of the control state, where the next state is related to the current state \ ``state``\ and the input \ ``ins``\, which belongs to the Mealy type state machine.

.. code:: verilog

   //PART B: Next-state combinational logic
   always @*
   begin
   case(state)
   S1:     begin
               if (ins==NOP) next_state=S0;
               else if (ins==HLT)  next_state=S2;
               else if (ins==PRE | ins==ADD) next_state=S9;
               else if (ins==LDM) next_state=S11;
               else next_state=S3;
           end

   S4:     begin
               if (ins==LDA | ins==LDO) next_state=S5;
               //else if (ins==STO) next_state=S7; 
               else next_state=S7; // ---Note: there are only 3 long instrucions. So, all the cases included. if (counter_A==2*b11)
           end
   Sidle:  next_state=S0;
   S0:     next_state=S1;
   S2:     next_state=S2;
   S3:     next_state=S4;
   S5:     next_state=S6;
   S6:     next_state=S0;
   S7:     next_state=S8;
   S8:     next_state=S0;
   S9:     next_state=S10;
   S10:    next_state=S0;
   S11:    next_state=S12;
   S12:    next_state=S0;
   default: next_state=Sidle;
   endcase
   end

4.4 Output combinatorial logic of FSM
~~~~~~~~~~~~~~~~~~~~~~

The output combinational logic circuit determines the output value according to the current state and the input command.

Due to the length of the paper, see the appendix.

5. Test and Results
--------------

In order to verify whether the RISC CPU function is correct or not, the chip is tested below.

5.1 Test Instructions
~~~~~~~~~~~~

The instructions stored in ROM are as follows：

.. code:: verilog

   // note: Decimal number in the bracket
   initial begin
       memory[0] = 8'b000_00000;   //NOP

       memory[1] = 8'b001_00001;   //LDO s1
       memory[2] = 8'b010_00001;   //rom(65)   //end, reg[1]<-rom[65]
       memory[3] = 8'b001_00010;   //LDO s2
       memory[4] = 8'b010_00010;   //rom(66)   //end, reg[2]<-rom[66]
       memory[5] = 8'b001_00011;   //LDO s3
       memory[6] = 8'b010_00011;   //rom(67)   //end, reg[3]<-rom[67] 

       memory[7] = 8'b100_00001;   //PRE s1
       memory[8] = 8'b101_00010;   //ADD s2
       memory[9] = 8'b110_00001;   //LDM s1  // REG[1] <- REG[1]+REG[2]
       
       memory[10] = 8'b011_00001;  //STO s1
       memory[11] = 8'b000_00001;  //ram(1)  // RAM[1] <- REG[1]
       memory[12] = 8'b010_00010;  //LDA s2
       memory[13] = 8'b000_00001;  //ram(1)  // REG[2] <- RAM[1]
       
       memory[14] = 8'b100_00011;  //PRE s3
       memory[15] = 8'b101_00010;  //ADD s2
       memory[16] = 8'b110_00011;  //LDM s3  // REG[3] <- REG[2]+REG[3]
       
       memory[17] = 8'b011_00011;  //STO s3
       memory[18] = 8'b000_00010;  //ram(2)   //REG[3] -> ram[2]
       memory[19] = 8'b111_00000;  //HLT   
       
       memory[65] = 8'b001_00101;  //37
       memory[66] = 8'b010_11001;  //89
       memory[67] = 8'b001_10101;  //53
   end

The instructions are executed in order, and the final result is to add the three numbers of 65, 66, and 67 bits in the ROM and store them in RAM[2], that is, to realize the addition of the three numbers, and at the same time, RAM[1] stores The sum of the addition of the first two numbers.

5.2 Test-Bench
~~~~~~~~~~~~~~

In order to test the function of the system, generate/write the test-bench file here for simulation:

.. code:: verilog

   `timescale 1ps / 1ps
   module core_tb_00  ; 
    
     reg    rst   ; 
     reg    clk   ; 
     core  
      DUT  ( 
          .rst (rst ) ,
         .clk (clk ) ); 

   // "Clock Pattern" : dutyCycle = 50
   // Start Time = 0 ps, End Time = 10 ns, Period = 100 ps
     initial
     begin
         clk  = 1'b0  ;
        # 150 ;
   // 50 ps, single loop till start period.
      repeat(99)
      begin
          clk  = 1'b1  ;
         #50  clk  = 1'b0  ;
         #50 ;
   // 9950 ps, repeat pattern in loop.
      end
         clk  = 1'b1  ;
        # 50 ;
   // dumped values till 10 ns
     end


   // "Constant Pattern"
   // Start Time = 0 ps, End Time = 10 ns, Period = 0 ps
     initial
     begin
         rst  = 1'b0  ;
        # 100;
       rst=1'b1;
        # 9000 ;
   // dumped values till 10 ns
     end

     initial
   #20000 $stop;
   endmodule

Only two signals need to be given to the CPU, the excitation clock \ ``clk``\ and the asynchronous reset signal \ ``rst``\.

5.3 Waveform
~~~~~~~~

|image17|

According to the ModelSIM simulation results, as shown in the figure above, the accumulator outputs the final result of 179. Before the final shutdown command (at 6300ps in the figure), the addr address is 2, the data is 179, and the ram write and enable signals are all 1, which will eventually The result is written into RAM[2], and the instruction instruction result is correct.

From the simulation waveform, not only the state of each control signal at each moment can be seen, but also the state transition information of the state machine executed by each instruction:

|image18|

As shown in the figure, it can be seen from the waveform that executing an LDO long instruction consumes 6 clock cycles, and the NOP instruction consumes two clock cycles, which is consistent with the state transition diagram, and the obtained result is consistent with the output requirements of the test command.

|image19|

The figure shows the two most important moments for verifying the correctness of the function. It can be seen from the waveform that the corresponding calculation results 126 and 179 are respectively written to the first and second positions of the RAM address, and the related control signals are normal. That is to achieve the function we designed. For more information about the waveform, see the attachment, the simulation source file.

6. Conclusion
--------

This article builds an 8-bit RISC
CPU, introduces the design process and experimental test in detail, including: hardware composition, instruction set system, etc. The focus is on the design of the controller. Based on the finite state machine, the correspondence and transfer between instructions and states has been realized, and a detailed simulation experiment has been carried out. The results prove that the CPU functions normally and meets expectations.

references
--------

[1] Zhou Heqin, Wu Xiuqing.
Microcomputer Principles and Interface Technology (Third Edition). University of Science and Technology of China Press. 2008.

appendix
----

**Appendix A Verilog Implementation of Controller**

.. code:: verilog

   module controller(ins, clk, rst, write_r, read_r, PC_en, fetch, ac_ena, ram_ena, rom_ena,ram_write, ram_read, rom_read, ad_sel);

   input clk, rst;         // clock, reset
   input [2:0] ins;        // instructions, 3 bits, 8 types

   // Enable signals
   output reg write_r, read_r, PC_en, ac_ena, ram_ena, rom_ena;

   // ROM: where instructions are storaged. Read only.
   // RAM: where data is storaged, readable and writable.
   output reg ram_write, ram_read, rom_read, ad_sel;

   output reg [1:0] fetch;     // 01: to fetch from RAM/ROM; 10: to fetch from REG

   // State code(current state)
   reg [3:0] state;        // current state
   reg [3:0] next_state;   // next state


   // instruction code
   parameter   NOP=3'b000, // no operation
               LDO=3'b001, // load ROM to register
               LDA=3'b010, // load RAM to register
               STO=3'b011, // Store intermediate results to accumulator
               PRE=3'b100, // Prefetch Data from Address
               ADD=3'b101, // Adds the contents of the memory address or integer to the accumulator
               LDM=3'b110, // Load Multiple
               HLT=3'b111; // Halt

   // state code            
   parameter Sidle=4'hf,
                S0=4'd0,
                S1=4'd1,
                S2=4'd2,
                S3=4'd3,
                S4=4'd4,
                S5=4'd5,
                S6=4'd6,
                S7=4'd7,
                S8=4'd8,
                S9=4'd9,
                S10=4'd10,
                S11=4'd11,
                S12=4'd12;
                
   //PART A: D flip latch; State register
   always @(posedge clk or negedge rst) 
   begin
       if(!rst) state<=Sidle;
           //current_state <= Sidle;
       else state<=next_state;
           //current_state <= next_state;  
   end

   //PART B: Next-state combinational logic
   always @*
   begin
   case(state)
   S1:     begin
               if (ins==NOP) next_state=S0;
               else if (ins==HLT)  next_state=S2;
               else if (ins==PRE | ins==ADD) next_state=S9;
               else if (ins==LDM) next_state=S11;
               else next_state=S3;
           end

   S4:     begin
               if (ins==LDA | ins==LDO) next_state=S5;
               //else if (ins==STO) next_state=S7; 
               else next_state=S7; // ---Note: there are only 3 long instrucions. So, all the cases included. if (counter_A==2*b11)
           end
   Sidle:  next_state=S0;
   S0:     next_state=S1;
   S2:     next_state=S2;
   S3:     next_state=S4;
   S5:     next_state=S6;
   S6:     next_state=S0;
   S7:     next_state=S8;
   S8:     next_state=S0;
   S9:     next_state=S10;
   S10:    next_state=S0;
   S11:    next_state=S12;
   S12:    next_state=S0;
   default: next_state=Sidle;
   endcase
   end

   // another style
   //PART C: Output combinational logic
   always@*
   begin 
   case(state)
   // --Note: for each statement, we concentrate on the current state, not next_state
   // because it is combinational logic.
     Sidle: begin
            write_r=1'b0;
            read_r=1'b0;
            PC_en=1'b0; 
            ac_ena=1'b0;
            ram_ena=1'b0;
            rom_ena=1'b0;
            ram_write=1'b0;
            ram_read=1'b0;
            rom_read=1'b0;
            ad_sel=1'b0;
            fetch=2'b00;
            end
        S0: begin // load IR
            write_r=0;
            read_r=0;
            PC_en=0;
    ac_ena=0;
            ram_ena=0;
            rom_ena=1;
            ram_write=0;
            ram_read=0;
            rom_read=1;
            ad_sel=0;
            fetch=2'b01;
            end
        S1: begin
            write_r=0;
            read_r=0;
            PC_en=1; 
            ac_ena=0;
            ram_ena=0;
            ram_write=0;
            ram_read=0;
            rom_ena=1;
            rom_read=1; 
            ad_sel=0;
            fetch=2'b00;
            end
        S2: begin
            write_r=0;
            read_r=0;
            PC_en=0;
            ac_ena=0;
            ram_ena=0;
            rom_ena=0;
            ram_write=0;
            ram_read=0;
            rom_read=0;
            ad_sel=0;
            fetch=2'b00;
            end
        S3: begin 
            write_r=0;
            read_r=0;
            PC_en=0;
            ac_ena=1; 
            ram_ena=0;
            rom_ena=1;
            ram_write=0;
            ram_read=0;
            rom_read=1;
            ad_sel=0;
            fetch=2'b10; 
            end
   S4: begin
            write_r=0;
            read_r=0;
            PC_en=1;
            ac_ena=1;
            ram_ena=0;
            ram_write=0;
            ram_read=0;
            rom_ena=1; 
            rom_read=1;
            ad_sel=0;
            fetch=2'b10; 
            end
        S5: begin
            if (ins==LDO)
            begin
            write_r=1;
            read_r=0;
            PC_en=0;
            ac_ena=1;
            ram_ena=0;
            ram_write=0;
            ram_read=0;
            rom_ena=1;
            rom_read=1;
            ad_sel=1;
            fetch=2'b01;        
            end
            else 
            begin
            write_r=1;
            read_r=0;
            PC_en=0;
            ac_ena=1;
            ram_ena=1;
            ram_write=0;
            ram_read=1;
            rom_ena=0;
            rom_read=0;
            ad_sel=1;
            fetch=2'b01;
            end     
            end
        S6: begin 

        write_r=1'b0;
            read_r=1'b0;
            PC_en=1'b0; //** not so sure, log: change 1 to 0
            ac_ena=1'b0;
            ram_ena=1'b0;
            rom_ena=1'b0;
            ram_write=1'b0;
            ram_read=1'b0;
            rom_read=1'b0;
            ad_sel=1'b0;
            fetch=2'b00;
       end

        S7: begin // STO, reg->ram. step1. read REG
            write_r=0;
            read_r=1;
            PC_en=0;
            ac_ena=0;
            ram_ena=0;
            rom_ena=0;
            ram_write=0;
            ram_read=0;
            rom_read=0;
            ad_sel=0;
            fetch=2'b00;
            end
        S8: begin // STO, step2, write RAM
            write_r=0;
            read_r=1;
            PC_en=0;
            ac_ena=0;
            rom_read=0;
            rom_ena=0;

            ram_ena=1;
            ram_write=1;
            ram_read=0;

            ad_sel=1;
            fetch=2'b00; //fetch=2'b10, ram_ena=1, ram_write=1, ad_sel=1;
            end
        S9: begin 
            if (ins==PRE) // REG->ACCUM
            begin
            write_r=0;
            read_r=1;
            PC_en=0;
            ac_ena=1;
            ram_ena=0;
            rom_ena=0;
            ram_write=0;
            ram_read=0;
            rom_read=0;
            ad_sel=0;
            fetch=2'b00;
            end
            else 
            begin 
            write_r=0;
            read_r=1;
            PC_en=0;
            ac_ena=1;
            ram_ena=0;
            rom_ena=0;
            ram_write=0;
            ram_read=0;
            rom_read=0;
            ad_sel=0;
    
            fetch=2'b00;        
            end 
            end
       S10: begin
            write_r=0;
            read_r=1;
            PC_en=0;
            ac_ena=0;
            ram_ena=0;
            rom_ena=0;
            ram_write=0;
            ram_read=0;
            rom_read=0;
            ad_sel=0;
            fetch=2'b00;
            end
       S11: begin // LDM, step1, write reg
            write_r=1;
            read_r=0;
            PC_en=0;
            ac_ena=1;
            ram_ena=0;
           
            ram_write=0;
            ram_read=0;
            rom_ena=1;
            rom_read=1;
            ad_sel=0;
            fetch=2'b00;
                   
            end
       S12: begin 
            write_r=0;
            read_r=0;
            PC_en=0;
            ac_ena=0;
            ram_ena=0;
            rom_ena=0;
            ram_write=0;
            ram_read=0;
            rom_read=0;
            ad_sel=0;
            fetch=2'b00;    
            end
   default: begin
            write_r=0;
            read_r=0;
            PC_en=0;
            ac_ena=0;
            ram_ena=0;
            rom_ena=0;
            ram_write=0;
            ram_read=0;
            rom_read=0;
            ad_sel=0;
            fetch=2'b00;        
            end
   endcase
   end
   endmodule

.. |image0| image:: assets/von.png
.. |image1| image:: assets/CPU-comp-right.png
.. |image2| image:: assets/rom.png
.. |image3| image:: assets/ram.png
.. |image4| image:: assets/pc.png
.. |image5| image:: assets/accum.png
.. |image6| image:: assets/mux.png
.. |image7| image:: assets/alu.png
.. |image8| image:: assets/reg.png
.. |image9| image:: assets/ir.png
.. |image10| image:: assets/schematic.png
.. |image11| image:: assets/RTL_Viewer_s.png
.. |image12| image:: assets/short-ins-caption.png
.. |image13| image:: assets/short-long-caption.png
.. |image14| image:: assets/fsm.png
.. |image15| image:: assets/s0.png
.. |image16| image:: assets/s1.png
.. |image17| image:: assets/wave.png
.. |image18| image:: assets/mv3.png
.. |image19| image:: assets/reg1.png

