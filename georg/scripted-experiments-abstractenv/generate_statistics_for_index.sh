INDEX=$1
OUTPUTDIR=data/config-$INDEX
OUTPUTFILE=$OUTPUTDIR/generate_statistics.$INDEX.out
rm -rf $OUTPUTDIR
mkdir -p $OUTPUTDIR
\time -o $OUTPUTFILE -a -p python ./generate_statistics.py $INDEX >$OUTPUTFILE 2>&1
