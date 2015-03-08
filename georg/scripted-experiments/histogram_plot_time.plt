hist(x)=floor(x*10)*0.1

set nokey

set boxwidth .1 

set title "Processing Time per Trace"
set xlabel "Processing Time per Trace [in seconds]"
set ylabel "Frequency"

set yrange[0:]

set datafile separator ","

set term unknown
plot data_file using (hist($27)):(1.0) smooth freq w boxes

set term pdf
set output output_file

set yrange[0:(GPVAL_Y_MAX+0.1*GPVAL_Y_MAX)]

plot data_file using (hist($27)):(1.0) smooth freq w boxes

