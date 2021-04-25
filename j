#
set -x
set -e
rm -f xx.json

ACCEXAMPLE=~/git/atomicc-examples/
RULEC=$ACCEXAMPLE/examples/echo

echo \
echo \
~/git/slang/build/bin/slang --single-unit --ast-json xx.json \
    -I$RULEC/generated -I$ACCEXAMPLE/lib/generated -I$ACCEXAMPLE/lib/verilog \
    -I$ACCEXAMPLE/../atomicc/simulation/verilog \
    -y $RULEC/generated -y $ACCEXAMPLE/lib/generated -y $ACCEXAMPLE/lib/verilog \
    -y $ACCEXAMPLE/../atomicc/simulation/verilog \
    --top VsimTop $ACCEXAMPLE/lib/generated/VsimTop.sv \
>/dev/null

echo \
~/git/slang/build/bin/slang --single-unit --ast-json xx.json -I$RULEC/generated \
    -I$ACCEXAMPLE/lib/generated -I$ACCEXAMPLE/lib/verilog \
    -I$ACCEXAMPLE/../atomicc/simulation/verilog \
    -y $RULEC/generated -y $ACCEXAMPLE/lib/generated -y $ACCEXAMPLE/lib/verilog \
    -y $ACCEXAMPLE/../atomicc/simulation/verilog \
    -y $ACCEXAMPLE/xilinx/import \
    --top ZynqTop $ACCEXAMPLE/lib/generated/ZynqTop.sv \

~/git/slang/build/bin/slang --ast-json xx.json \
    --error-limit=9999 \
    svaall.sv

./a.out
