/-
NPT.Cert.EP3D3.ClassL — class and witness lists by family.
-/
import NPT.Cert.EP3D3.Class0
import NPT.Cert.EP3D3.Class1
import NPT.Cert.EP3D3.Class2

namespace NPT.Cert.EP3D3

/-- Class data by family. -/
def clsL (f : ℕ) : List ℕ := if f = 0 then cls0 else if f = 1 then cls1 else cls2
def witL (f : ℕ) : List ℕ := if f = 0 then wit0 else if f = 1 then wit1 else wit2

end NPT.Cert.EP3D3
