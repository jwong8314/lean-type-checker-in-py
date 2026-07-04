set_option pp.all true
set_option pp.universes true
set_option pp.explicit true
set_option pp.notation false

#check (show @Eq Nat ((fun x : Nat => x) 2) 2 from rfl)
#check (@Eq.refl Nat 2 : @Eq Nat 2 2)
#check (show @Eq Nat ((fun x : Nat => x) 2) 2 from @Eq.refl Nat 2)

