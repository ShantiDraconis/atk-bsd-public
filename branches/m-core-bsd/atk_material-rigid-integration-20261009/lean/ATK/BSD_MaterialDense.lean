import MCore.Material.Closure
namespace ATK.BSD
abbrev Material (R T Q : Prop) : Prop := MCore.Material.MaterialBSDProducer R T Q

theorem producer_of_concrete {R T Q : Prop}
    (h : MCore.Material.BSDClosure R T Q) : Material R T Q := ⟨h⟩
end ATK.BSD
#print axioms ATK.BSD.producer_of_concrete
