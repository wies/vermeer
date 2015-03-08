hist(x)=floor(x)

set nokey

set boxwidth .5 

set title "Processing Time per Trace"
set xlabel "Processing Time per Trace [in seconds]"
set ylabel "Frequency"
#set grid

#set xrange[-10:110]
set yrange[0:]

#set format x "%10.0f%%"

set datafile separator ","

set term unknown
plot "data_option1.filtered.dat" using (hist($27)):(1.0) smooth freq w boxes

set term png
set output "histogram_plot_time.png"

set yrange[0:(GPVAL_Y_MAX+0.1*GPVAL_Y_MAX)]

plot "data_option1.filtered.dat" using (hist($27)):(1.0) smooth freq w boxes

