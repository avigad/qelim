import ...mathlib.data.int.basic

set_option class.instance_max_depth 256

namespace int 

def foobar (i j : int) : Prop := (has_dvd.dvd i j)

end int