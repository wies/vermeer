set nokey

set datafile separator ","

set title "Number of Variables (total)"
set xlabel "Reduced (total)"
set ylabel "Initial (total)"
set grid

set term unknown
plot 'data.txt' using 5:8

max = (GPVAL_Y_MAX > GPVAL_X_MAX ? GPVAL_Y_MAX : GPVAL_X_MAX)

set term png
set output "scatter_plot_variables.png"

set xrange[0:max]
set yrange[0:max]

set size ratio -1

plot 'data.txt' using 5:8
quit
