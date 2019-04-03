/*
 * This module is generic formal scoreboard for data integrity checks
 * This scoreboard implements counter technique
 * This technique is very useful when verifying systems that process
 * data in-order. This technique cannot be used for systems that process
 * data out-of-order. The Wolper technique is appropriate in that scenario.
 *
 * Author: Mandar Munishwar (verifymychip@gmail.com)
 *
 * Date: March 21, 2019
 *
 */
module fv_sb_inorder #(
  parameter DWIDTH = 4,
  parameter MAX_TRANS = 16
) (
  input logic clk,
  input logic rstn,
  input logic push_valid,
  input logic [DWIDTH-1:0] push_data,
  input logic pop_valid,
  input logic [DWIDTH-1:0] pop_data,
  output logic [$clog2(MAX_TRANS):0] cntr // This output is for debug
);

logic sample_now;
logic sampled_in, sampled_out;
logic [DWIDTH-1:0] tracked_data;
logic [DWIDTH-1:0] junk_data;
logic [$clog2(MAX_TRANS):0] cntr_next;
logic cntr_incr, cntr_decr;
logic compare_now;

/*
 * sample_now is a symbolic (or non-deterministic) variable, it does not
 * have any driver and it is uninitialized. The formal tools will set its value
 * at any time (thats the magic of formal).
 * cntr - this counts the number of transactions in flight, it increments
 * when data enters the system (push_valid) and decrements when data exits the
 * system (pop_valid).
 * When sample_now is asserted, the scoreboard records the incoming data
 * into tracked_data variable and sets the flag sampled_in
 * This flag is used to stop incrementing the counter after data is sampled in
 * which means, counter value tells us how many entries are queued before
 * sampled data.
 * As data starts exiting, the counter keeps decrementing, when counter reaches
 * 1, thats the position where our sampled data is. we mark that condition
 * as variable compare_now, and use that in the assertion to compare pop_data
 * with our stored data (tracked_data). If for any reason the system is
 * not processing data in-order, the data integrity check will fail
 *
 */

always @(posedge clk or negedge rstn) begin
  if (!rstn) begin
    cntr <= '0;
    sampled_in <= 1'b0;
    sampled_out <= 1'b0;
  end else begin
    cntr <= cntr_next;
    sampled_in <= sample_now && push_valid ? 1'b1 : sampled_in;
    tracked_data <= sample_now && cntr_incr ? push_data : tracked_data;
    sampled_out <= compare_now ? 1'b1 : sampled_out;
  end
end

assign cntr_incr = push_valid && !sampled_in;
assign cntr_decr = pop_valid && !sampled_out;

assign cntr_next = cntr + cntr_incr - cntr_decr;
assign compare_now = (cntr == 1) && sampled_in && cntr_decr;

chk_data_forward_progress_ast:
                assert property (@(posedge clk) disable iff (!rstn)
                  sampled_in |-> s_eventually sampled_out);

chk_data_integrity_ast:
                assert property (@(posedge clk) disable iff (!rstn)
                  compare_now |-> (pop_data == tracked_data));

/*
 * Purpose of this assertion is to make sure that our assumption about
 * maximum transactions that can be pending is correct, our counter has been
 * sized based on this parameter, if this assertion fails, the parameter
 * MAX_TRANS will need to be adjusted
 *
 */
chk_counter_sanity_ast:
                assert property (@(posedge clk) disable iff (!rstn)
                   (cntr <= MAX_TRANS));

endmodule: fv_sb_inorder
