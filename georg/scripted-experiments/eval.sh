INDEX=$1
OUTPUTDIR=data/config-$INDEX
OUTPUTFILE=$OUTPUTDIR/generate_statistics.$INDEX.out
FAULTY_DAT_FILE=$OUTPUTDIR/data_option$INDEX.faulty.dat
FILTERED_DAT_FILE=$OUTPUTDIR/data_option$INDEX.filtered.dat
ERROR_MESSAGES_FILE=$OUTPUTDIR/error_messages.$INDEX.txt
HISTOGRAM_TIME_PDF=$OUTPUTDIR/histogram_time.data_option$INDEX.filtered.pdf
HISTOGRAM_STMTS_PDF=$OUTPUTDIR/histogram_statements.data_option$INDEX.filtered.pdf
SCATTER_PLOT_STMTS_PDF=$OUTPUTDIR/scatter_plot_statements.data_option$INDEX.filtered.pdf
SCATTER_PLOT_CSS_PDF=$OUTPUTDIR/scatter_plot_context_switches.data_option$INDEX.filtered.pdf
SCATTER_PLOT_VARS_PDF=$OUTPUTDIR/scatter_plot_variables.data_option$INDEX.filtered.pdf

python check_data_file.py $INDEX
python filter_error_messages.py $FAULTY_DAT_FILE $OUTPUTFILE > $ERROR_MESSAGES_FILE
./histogram_plot_time.sh $FILTERED_DAT_FILE $HISTOGRAM_TIME_PDF
./histogram_plot_statements.sh $FILTERED_DAT_FILE $HISTOGRAM_STMTS_PDF
./scatter_plot_statements.sh $FILTERED_DAT_FILE $SCATTER_PLOT_STMTS_PDF
./scatter_plot_context_switches.sh $FILTERED_DAT_FILE $SCATTER_PLOT_CSS_PDF
./scatter_plot_variables.sh $FILTERED_DAT_FILE $SCATTER_PLOT_VARS_PDF

