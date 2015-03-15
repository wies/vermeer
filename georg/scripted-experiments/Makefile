clean:
	rm generate_statistics.*.out
	rm data_option*.dat

all: option0 option1 option2

option0:
	./generate_statistics_for_index.sh 0

eval0:
	python check_data_file.py 0
#	./histogram_plot_time.sh data_option0.filtered.dat histogram_time.data_option0.filtered.pdf
#	./histogram_plot_statements.sh data_option0.filtered.dat histogram_statements.data_option0.filtered.pdf
#	./scatter_plot_statements.sh data_option0.filtered.dat scatter_plot_statements.data_option0.filtered.pdf
#	./scatter_plot_context_switches.sh data_option0.filtered.dat scatter_plot_context_switches.data_option0.filtered.pdf
#	./scatter_plot_variables.sh data_option0.filtered.dat scatter_plot_variables.data_option0.filtered.pdf
	python filter_error_messages.py data/config-0/data_option0.faulty.dat data/config-0/generate_statistics.0.out > data/config-0/error_messages.0.txt

option1:
	./generate_statistics_for_index.sh 1

eval1:
	python check_data_file.py 1
#	./histogram_plot_time.sh data_option1.filtered.dat histogram_time.data_option1.filtered.pdf
#	./histogram_plot_statements.sh data_option1.filtered.dat histogram_statements.data_option1.filtered.pdf
#	./scatter_plot_statements.sh data_option1.filtered.dat scatter_plot_statements.data_option1.filtered.pdf
#	./scatter_plot_context_switches.sh data_option1.filtered.dat scatter_plot_context_switches.data_option1.filtered.pdf
#	./scatter_plot_variables.sh data_option1.filtered.dat scatter_plot_variables.data_option1.filtered.pdf
	python filter_error_messages.py data/config-1/data_option1.faulty.dat data/config-1/generate_statistics.1.out > data/config-1/error_messages.1.txt

option2:
	./generate_statistics_for_index.sh 2

eval2:
	python check_data_file.py 2
#	./histogram_plot_time.sh data_option2.filtered.dat histogram_time.data_option2.filtered.pdf
#	./histogram_plot_statements.sh data_option2.filtered.dat histogram_statements.data_option2.filtered.pdf
#	./scatter_plot_statements.sh data_option2.filtered.dat scatter_plot_statements.data_option2.filtered.pdf
#	./scatter_plot_context_switches.sh data_option2.filtered.dat scatter_plot_context_switches.data_option2.filtered.pdf
#	./scatter_plot_variables.sh data_option2.filtered.dat scatter_plot_variables.data_option2.filtered.pdf
	python filter_error_messages.py data/config-2/data_option2.faulty.dat data/config-2/generate_statistics.2.out > data/config-2/error_messages.2.txt

option3:
	./generate_statistics_for_index.sh 3

option4:
	./generate_statistics_for_index.sh 4

option5:
	./generate_statistics_for_index.sh 5

option6:
	./generate_statistics_for_index.sh 6

eval6:
	python check_data_file.py 6
#	./histogram_plot_time.sh data_option6.filtered.dat histogram_time.data_option6.filtered.pdf
#	./histogram_plot_statements.sh data_option6.filtered.dat histogram_statements.data_option6.filtered.pdf
#	./scatter_plot_statements.sh data_option6.filtered.dat scatter_plot_statements.data_option6.filtered.pdf
#	./scatter_plot_context_switches.sh data_option6.filtered.dat scatter_plot_context_switches.data_option6.filtered.pdf
#	./scatter_plot_variables.sh data_option6.filtered.dat scatter_plot_variables.data_option6.filtered.pdf
	python filter_error_messages.py data/config-6/data_option6.faulty.dat data/config-6/generate_statistics.6.out > data/config-6/error_messages.6.txt

option7:
	./generate_statistics_for_index.sh 7

eval7:
	python check_data_file.py 7
	./histogram_plot_time.sh data_option7.filtered.dat histogram_time.data_option7.filtered.pdf
	./histogram_plot_statements.sh data_option7.filtered.dat histogram_statements.data_option7.filtered.pdf
	./scatter_plot_statements.sh data_option7.filtered.dat scatter_plot_statements.data_option7.filtered.pdf
	./scatter_plot_context_switches.sh data_option7.filtered.dat scatter_plot_context_switches.data_option7.filtered.pdf
	./scatter_plot_variables.sh data_option7.filtered.dat scatter_plot_variables.data_option7.filtered.pdf
	python filter_error_messages.py data_option7.faulty.dat generate_statistics.7.out > error_messages.7.txt

option8:
	./generate_statistics_for_index.sh 8

option9:
	./generate_statistics_for_index.sh 9

option10:
	./generate_statistics_for_index.sh 10

