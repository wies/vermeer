hist(x, y)=floor(10*(x-y)/x)*10

set nokey

set boxwidth 9 

set title "Reduction of Statements (total)"
set xlabel "Reduction of Statements [in %]"
set ylabel "Frequency"

set xrange[-10:110]
set yrange[0:]

set format x "%10.0f%%"

set datafile separator ","

set term unknown
plot data_file using (hist($4,$7)):(1.0) smooth freq w boxes

set term pdf
set output output_file

set yrange[0:(GPVAL_Y_MAX+0.1*GPVAL_Y_MAX)]

plot data_file using (hist($4,$7)):(1.0) smooth freq w boxes

