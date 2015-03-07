set nokey

set datafile separator ","

set title "Number of Context Switches (total)"
set xlabel "Reduced (total)"
set ylabel "Initial (total)"
set grid

set term unknown
plot 'data.txt' using 4:7

max = (GPVAL_Y_MAX > GPVAL_X_MAX ? GPVAL_Y_MAX : GPVAL_X_MAX)

set term png
set output "scatter_plot_context_switches.png"

set xrange[0:max]
set yrange[0:max]

set size ratio -1

plot 'data.txt' using 3:6
quit
