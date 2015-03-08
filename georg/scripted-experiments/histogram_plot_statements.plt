hist(x, y)=floor(10*(x-y)/x)*10

set nokey

set boxwidth 10 

set title "Reduction of Statements (total)"
set xlabel "Reduction of Statements [in %]"
set ylabel "Frequency"
#set grid

set xrange[-10:110]
set yrange[0:]

set format x "%10.0f%%"

set datafile separator ","

set term unknown
plot "data_option1.cleanedup.txt" using (hist($4,$7)):(1.0) smooth freq w boxes

set term png
set output "histogram_plot_statements.png"

set yrange[0:(GPVAL_Y_MAX+0.1*GPVAL_Y_MAX)]

plot "data_option1.cleanedup.txt" using (hist($4,$7)):(1.0) smooth freq w boxes
