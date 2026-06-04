import sys
from convert import wrap_for_main
open('/tmp/cur.py','w').write(wrap_for_main(open(sys.argv[1]).read()))
