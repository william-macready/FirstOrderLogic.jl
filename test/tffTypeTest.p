%------------------------------------------------------------------------
tff(animal_type,type, animal: $tType ).
tff(cat_type,type, cat: $tType ).
tff(dog_type,type, dog: $tType ).
tff(human_type,type, human: $tType ).
tff(cat_to_animal_type,type, cat_to_animal: cat > animal ).
tff(dog_to_animal_type,type, dog_to_animal: dog > animal ).
tff(garfield_type,type, garfield: cat ).
tff(odie_type,type, odie: dog ).
tff(jon_type,type, jon: human ).
tff(owner_of_type,type, owner_of: animal > human ).
tff(chased_type,type, chased: ( dog * cat ) > $o ).
tff(hates_type,type, hates: ( human * human ) > $o ).

tff(human_owner,axiom, ! [A: animal] : ? [H: human] : H = owner_of(A) ).
tff(jon_owns_garfield,axiom, jon = owner_of(cat_to_animal(garfield)) ).
tff(jon_owns_odie,axiom, jon = owner_of(dog_to_animal(odie)) ).
tff(jon_owns_only,axiom,
    ! [A: animal] :
    ( jon = owner_of(A)
    => ( A = cat_to_animal(garfield) | A = dog_to_animal(odie) ) ) ).
tff(dog_chase_cat,axiom,
    ! [C: cat,D: dog] :
    ( chased(D,C)
    => hates(owner_of(cat_to_animal(C)),owner_of(dog_to_animal(D))) ) ).
tff(odie_chased_garfield,axiom, chased(odie,garfield) ).
tff(jon_hates_jon,conjecture, hates(jon,jon) ).
%------------------------------------------------------------------------
