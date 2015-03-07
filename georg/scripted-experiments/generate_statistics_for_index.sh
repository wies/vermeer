INDEX=$1
OUTPUTFILE=generate_statistics.$INDEX.out
\time -o $OUTPUTFILE -a -p python ./generate_statistics.py $INDEX >$OUTPUTFILE 2>&1
