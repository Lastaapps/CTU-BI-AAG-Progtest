 #!bin/bash
 
 #Bash script to convert ALT output to a struct in C++
 #Author: Pavel Kolsky, Jaroslav Knapek
 #Usage: ./translate -filename(ALT text output)
 
 ORIGINAL=$(<$1)
 
 #get all the states
 STATES=$(echo $ORIGINAL|grep -o -P '(?<=states = ).*(?=inputAlphabet)')
 
 #get all the symbols
 SYM_TEMP=$(echo $ORIGINAL| grep -o -P '(?<=inputAlphabet = ).*(?=initialState)' | tr -d " "|tr -d "}"|tr -d "{")
 
SYMBOLS=$(echo $SYM_TEMP|sed 's/\([[:alnum:]]\)/'\''\1'\''/g'|awk '{print "{"$0"}"}')

#Get the initial state
INITIAL=$(echo $ORIGINAL|grep -o -P '(?<=initialState = ).*(?=finalStates)')

#Get the final states
FINAL=$(echo $ORIGINAL|grep -o -P '(?<=finalStates = ).*(?=transitions)')

#Get the original transitions
ORIG_TRANSITIONS=$(echo $ORIGINAL|awk -F"transitions = " '{print $2}')

PARSED_TRANSITIONS=$(echo "$ORIG_TRANSITIONS"| sed 's/[{}]//g' | sed 's/.$//' | sed 's/ //g' | sed 's/\([^,]*,[^,]*,[^,]*\),/\1\n/g' | sed 's/(/,/g' | sed 's/)/,/g' | sed 's/,,/,/g' | sed 's/^.//' | sed 's/.$//')

CONVERTED_TRANSITIONS=$(echo "$PARSED_TRANSITIONS" | awk -F"," '{print "\t\t{{"$1",\047"$2"\047},{"  $3"}},"}')


if [ $ORIG_TRANSITIONS == "{})" ]
then
CONVERTED_TRANSITIONS="{}"
fi

printf "NFA test {\n %s,\n %s,\n\t{\n %s\n\t},\n %s,\n %s\n};\n" "$STATES" "$SYMBOLS" "$CONVERTED_TRANSITIONS" "$INITIAL" "$FINAL"

