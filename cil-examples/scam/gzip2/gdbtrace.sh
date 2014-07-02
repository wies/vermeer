#!/bin/bash

TMP_FILE=tmp.file

if [ -z $1 ]; then
    echo "Input file not provided."
    exit
elif [ ! -f $1 ]; then
    echo "Cannot open $1."
    exit
fi

cat > $TMP_FILE <<EOI
define step_until_die
while (\$_isvoid(\$_exitcode) && \$_isvoid(\$_exitsignal))
step
end
end
b main
EOI
echo -n 'r ' >> $TMP_FILE

LINES=`wc -l $1 | cut -f1 -d' '`
for ((I=1; I<=LINES; I=I+1)); do
    if [ $I -eq $LINES ]; then
        tail -n +$I $1 | head -1 | sed -e 's/^\.\/gzip //' >> $TMP_FILE
    else
        tail -n +$I $1 | head -1 | sed -e 's/^\.\/gzip //' -e 's/$/\\/' >> $TMP_FILE
    fi
done

echo step_until_die >> $TMP_FILE

gdb ./gzip > out_trace_$1.txt < $TMP_FILE

rm -f $TMP_FILE
