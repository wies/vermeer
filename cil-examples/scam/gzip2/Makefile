.PHONY: clean gdbtrace

gzip: allfile.c crypt.h getopt.h gzip.h lzw.h revision.h tailor.h               
	./tender.sh allfile.c -DSTDC_HEADERS=1 -DHAVE_UNISTD_H=1 -DDIRENT=1 -DHAVE_ALLOCA_H=1 -DFAULTY_F_KL_1
	gcc -g -o gzip allfile.tendered.c                                       

gdbtrace: gzip
	./gdbtrace.sh input000001
                                                                                
clean:                                                                          
	rm -f gzip allfile.c.tmp_in allfile.c.tmp_out allfile.tendered.c out_trace_input000001.txt
