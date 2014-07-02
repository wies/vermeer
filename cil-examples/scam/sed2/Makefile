.PHONY: clean gdbtrace

sed: FaultSeeds.h getopt.h rx.h sed.c
	./tender.sh sed.c -DFAULTY_F_AG_19
	gcc -g -o sed sed.tendered.c

gdbtrace: sed
	./gdbtrace.sh input000001

clean:
	rm -f sed sed.tendered.c sed.c.tmp_in sed.c.tmp_out out_trace_input000001.txt tmp.file
