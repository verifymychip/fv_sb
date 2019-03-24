/*
 * This module is generic formal scoreboard for data integrity checks
 * This scoreboard implements Wolper Technique.
 * (also known as sequence abstraction)
 *
 * Reference : https://www.semiwiki.com/forum/content/7537-wolper-method.html
 *
 * Author: Mandar Munishwar (verifymychip@gmail.com)
 *
 * Date: March 21, 2019
 *
 */
module fv_sb_wolper #(
  parameter DWIDTH = 4
) (
  input logic clk,
  input logic rstn,
  input logic push_valid,
  input logic [DWIDTH-1:0] push_data,
  input logic pop_valid,
  input logic [DWIDTH-1:0] pop_data
);
/*
 * Premise of Wolper's theory is that if control and payload data are
 * independent, then for verification, the actual data values does not matter.
 * We take advantage of this and constrain the input data (push_data)
 * such that, we allow a specific value to enter the system only once,
 * and then on the output we observe that
 *    1) if the specific value has not entered, we should not see it at output
 *    2) if we have seen the specific value at input, we should see it at
 *       output eventually (or we can add a bounded check)
 *    3) If we have seen the specific value at output, we should never see it
 *       again at the output (no duplication)
 * This technique is particularly useful when when creating formal scoreboards
 * for verifying systems that may process data out-of-order.
 */
logic [DWIDTH-1:0] special_data;
special_data_is_stable_asm:
                assume property (@(posedge clk) disable iff (!rstn)
                      ##1 $stable(special_data));

logic special_data_seen_at_input;
always_ff @(posedge clk or negedge rstn) begin
  if (!rstn) begin
    special_data_seen_at_input <= 1'b0;
  end else begin
    if (push_valid && (push_data == special_data)) begin
      special_data_seen_at_input <= 1'b1;
    end
  end
end
send_special_data_only_once_asm:
                assume property (@(posedge clk) disable iff (!rstn)
                    special_data_seen_at_input && push_valid
                    |-> (push_data != special_data));

logic special_data_seen_at_output;
always_ff @(posedge clk or negedge rstn) begin
  if (!rstn) begin
    special_data_seen_at_output <= 1'b0;
  end else begin
    if (push_valid && (pop_data == special_data)) begin
      special_data_seen_at_output <= 1'b1;
    end
  end
end

// Checks
chk_data_causality_ast:
                assert property (@(posedge clk) disable iff (!rstn)
                  !special_data_seen_at_input && pop_valid
                  |-> (pop_data != special_data));

chk_data_forward_progress_ast:
                assert property (@(posedge clk) disable iff (!rstn)
                  special_data_seen_at_input
                  |-> s_eventually (pop_valid && (pop_data == special_data)));

chk_data_no_duplication_ast:
                assert property (@(posedge clk) disable iff (!rstn)
                  special_data_seen_at_output && pop_valid
                  |-> (pop_data != special_data));

endmodule: fv_sb_wolper
