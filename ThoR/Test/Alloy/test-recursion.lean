-- test from org.alloytools.alloy.core/src/test/resources/test-recursion.als

import ThoR

~alloy test_recursion
  sig Foo { n : lone Foo }
  pred a[ f : Foo ] { some f.n implies b[f.n] }
  pred b[ f : Foo ] { some f.n implies a[f.n] }
end
