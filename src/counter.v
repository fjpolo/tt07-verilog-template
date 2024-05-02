`default_nettype none

module counter(
    input clk_i,
    input n_reset_i,
    input ce_i,
    output output_active_o
);

reg [6:0] counter;
`ifdef FORMAL
initial counter = 7'h00;
`endif 

localparam MAX_COUNT = 127;

always @(posedge clk_i) begin
    if((!n_reset_i))
        counter <= 8'h00;
    else begin
        if(ce_i) begin
            counter <= counter + 1;
        end
    end
end

assign output_active_o = (counter == MAX_COUNT);

//
// FORMAL VERIFICATION
//
`ifdef FORMAL

    `ifdef COUNTER
		`define	ASSUME	assume
	`else
		`define	ASSUME	assert
	`endif

    // f_past_valid
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge clk_i)
		f_past_valid <= 1'b1;

    // Prove that n_reset_i works correctly
    always @(posedge clk_i)
        if((f_past_valid)&&($past(!n_reset_i)&&(n_reset_i)))
            assert(counter == 8'h00);

    // Prove that output_active_o is assigned correctly
    always @(*)
        if((n_reset_i)&&(f_past_valid)&&(ce_i))
            assert(output_active_o <= (counter == MAX_COUNT));

    // Prove that counter is never > MAX_COUNT
    initial assert(counter == 8'h00);
    always @(*) begin
        if(f_past_valid) begin
            assert(counter <= MAX_COUNT);
        end
    end

    //
    // Contract
    //
    always @(posedge clk_i) begin
        if((n_reset_i)&&($past(n_reset_i))&&(f_past_valid)) begin
            // Prove that counter counts - Two consecutive ce_i clocks
            if($past(ce_i)) begin
                if($past(counter) >= MAX_COUNT)
                    assert(counter == 8'h00);
                else 
                    assert(counter == ($past(counter)+1));
            // Prove that counter counts - ce_i clock following !ce_i clock
            end else begin
                assert(counter == $past(counter));
            end
        end
    end

`endif // FORMAL

endmodule