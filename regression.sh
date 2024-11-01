echo "<<<Regression testing>>>"
echo ""
echo "/---\\"
echo "|abs|"
echo "\\---/"
python3 app.py --include examples examples/abs.c examples/abs.tests
echo ".. should both work"

echo ""
echo "/----\\"
echo "|bits|"
echo "\\----/"
python3 app.py --pbt --include examples examples/bits.c examples/bits.tests
echo ".. should work with pbt"
python3 app.py --unwind 32 --include examples examples/bits.c examples/bits.tests
echo ".. should work"


echo ""
echo "/---\\"
echo "|gcd|"
echo "\\---/"
python3 app.py --include examples examples/gcd.c examples/gcd.tests
echo ".. should both fail"


echo ""
echo "/----\\"
echo "|loop|"
echo "\\----/"
python3 app.py --pbt --pbttries 100 --include examples examples/loop.c examples/loop.tests
echo "... should fail with PBT"


echo ""
echo "/---\\"
echo "|max|"
echo "\\---/"
python3 app.py --include examples examples/max.c examples/max.tests
echo "... should all work except max_test_1"


echo ""
echo "/------\\"
echo "|memory|"
echo "\\------/"
python3 app.py --include examples examples/memory.c examples/memory.tests --memfile examples/memory.mem --memory --unwind 5
echo "... should work"


echo ""
echo "/----------\\"
echo "|merge_sort|"
echo "\\----------/"
python3 app.py --include examples examples/merge_sort.c examples/merge_sort.tests --memfile examples/merge_sort.mem --memory --unwind 4
echo "... should work"



echo ""
echo "/-------\\"
echo "|sorting|"
echo "\\-------/"
python3 app.py --include examples examples/sorting.c examples/sorting.tests --unwind 5
echo "... should first work, last two fail"


echo ""
echo "/-----\\"
echo "|stack|"
echo "\\-----/"
python3 app.py --include examples examples/stack.c examples/stack.tests --unwind 10
echo "... should all work"


echo ""
echo "/---\\"
echo "|sum|"
echo "\\---/"
python3 app.py --include examples examples/sum.c examples/sum.tests --unwind 40
echo "... should fail"


echo ""
echo "/--------\\"
echo "|triangle|"
echo "\\--------/"
python3 app.py --include examples examples/triangle.c examples/triangle.tests
echo "... should all work except last one"
