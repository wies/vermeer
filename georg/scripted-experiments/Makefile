clean:
	rm generate_statistics.*.out
	rm data_option*.dat

all: option0 option1 option2

option0:
	./generate_statistics_for_index.sh 0

eval0:
	python check_data_file.py 0
	./histogram_plot_time.sh data_option0.filtered.dat histogram_time.data_option0.filtered.pdf
	./histogram_plot_statements.sh data_option0.filtered.dat histogram_statements.data_option0.filtered.pdf
	./scatter_plot_statements.sh data_option0.filtered.dat scatter_plot_statements.data_option0.filtered.pdf
	./scatter_plot_context_switches.sh data_option0.filtered.dat scatter_plot_context_switches.data_option0.filtered.pdf
	./scatter_plot_variables.sh data_option0.filtered.dat scatter_plot_variables.data_option0.filtered.pdf

option1:
	./generate_statistics_for_index.sh 1

eval1:
	python check_data_file.py 1
	./histogram_plot_time.sh data_option1.filtered.dat histogram_time.data_option1.filtered.pdf
	./histogram_plot_statements.sh data_option1.filtered.dat histogram_statements.data_option1.filtered.pdf
	./scatter_plot_statements.sh data_option1.filtered.dat scatter_plot_statements.data_option1.filtered.pdf
	./scatter_plot_context_switches.sh data_option1.filtered.dat scatter_plot_context_switches.data_option1.filtered.pdf
	./scatter_plot_variables.sh data_option1.filtered.dat scatter_plot_variables.data_option1.filtered.pdf

option2:
	./generate_statistics_for_index.sh 2

eval2:
	python check_data_file.py 2
	./histogram_plot_time.sh data_option2.filtered.dat histogram_time.data_option2.filtered.pdf
	./histogram_plot_statements.sh data_option2.filtered.dat histogram_statements.data_option2.filtered.pdf
	./scatter_plot_statements.sh data_option2.filtered.dat scatter_plot_statements.data_option2.filtered.pdf
	./scatter_plot_context_switches.sh data_option2.filtered.dat scatter_plot_context_switches.data_option2.filtered.pdf
	./scatter_plot_variables.sh data_option2.filtered.dat scatter_plot_variables.data_option2.filtered.pdf

option3:
	./generate_statistics_for_index.sh 3

option4:
	./generate_statistics_for_index.sh 4

option5:
	./generate_statistics_for_index.sh 5

option6:
	./generate_statistics_for_index.sh 6

option7:
	./generate_statistics_for_index.sh 7

eval7:
	python check_data_file.py 7
	./histogram_plot_time.sh data_option7.filtered.dat histogram_time.data_option7.filtered.pdf
	./histogram_plot_statements.sh data_option7.filtered.dat histogram_statements.data_option7.filtered.pdf
	./scatter_plot_statements.sh data_option7.filtered.dat scatter_plot_statements.data_option7.filtered.pdf
	./scatter_plot_context_switches.sh data_option7.filtered.dat scatter_plot_context_switches.data_option7.filtered.pdf
	./scatter_plot_variables.sh data_option7.filtered.dat scatter_plot_variables.data_option7.filtered.pdf

option8:
	./generate_statistics_for_index.sh 8

option9:
	./generate_statistics_for_index.sh 9

option10:
	./generate_statistics_for_index.sh 10

