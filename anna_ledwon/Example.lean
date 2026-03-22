import Mathlib
-- loads the entire mathlib library into the file
-- needed for instance for ℝ, Fin 3, Set, by_cases!

variable {α : Type*}
-- Let `α` be a type.
-- A declaration of an implicit universe-polymorphic type variable
-- type variable α is placeholder for a type that can be filled in later, Lean knows "assume some type exists"
-- implicit is done through curly brackets {}; Lean can now figure out what α is from context and will not have to be told every time
-- universe-polymorphic: Type* means α lives in some universe level, we don't care which
-- in total: "Fix a carrier set, but do not commit to what it is."



-- DEFINITION OF SPACE AND POSTULATE 2 (THE DISTANCE POSTULATE)
-- A "space" is a type with a bijection to ℝ³.
-- Space α is a structure that equips the type α with a bijection to ℝ³.
-- The elements of α are points, and coord tells us how to interpret each point as coordinates in 3-dimensional space.

-- DEFINITION OF SPACE + POSTULATE 2
structure Space (α : Type*) where
  coord : α ≃ (Fin 3 → ℝ)
  -- space takes as input α : Type*, Space α itself is a type
  -- Given a type α, Space α is the type of ways to equip α with the structure of a “space”
  -- coord : α ≃ (Fin 3 → ℝ) introduces a field of the structure Space where ≃ is the type of bijections (equivalences) between types
  -- the function type Fin 3 → ℝ is the type of functions from {0, 1, 2} to ℝ, i.e. triples of real numbers

  -- POSTULATE 2 : THE DISTANCE POSTULATE
  dist : α → α → ℝ
  dist_symm : ∀ p q : α, dist p q = dist q p
  dist_self : ∀ p q : α, p = q → dist p q = 0
  dist_pos : ∀ p q : α, p ≠ q → dist p q > 0




/- In case the parameter α is actually never needed, you can instead replace α by `Fin 3 → ℝ`
everywhere, so the first line would read
structure Objects (S : Space (Fin 3 → ℝ)) where
-/

-- Geometric objects we are considering: all points, all lines, all planes
-- with their axiomatic properties.

-- A point is "an element of" our space.
variable (α) in           -- "scope control" following uses α, but does not introduce a global α
abbrev Points := α         -- a definitional abbreviation, α and Points α are definitionally equal, i.e. the "set" of all points.
-- We are saying α = raw carrier type, while Point α = elements of that type viewed as points


structure Line (S : Space α) where
  carrier : Set α

-- part of POSTULATE 3 : THE RULER POSTULATE
structure LineWithCoordinate (S : Space α) extends Line S where
  coordinate : carrier ≃ ℝ



instance (S : Space α) : SetLike (Line S) α where
  coe l := l.carrier
  coe_injective' := by
    intro ⟨l⟩ ⟨l'⟩ h
    cases h
    rfl
  -- can also be proved shorter wiht simp_all



---------------------------------------------------- Start of structure Objects (containing all postulates!)
------------------------------------------------------------------------------

-- For our purposes this structure will not be used but can be used for geometries that do not use coordinates.
structure Objects (S : Space α) where
    /- The set of all the lines in our space -/
    lines : Set (Line S)
    /- The line defined by two points. Uses a junk value if the points are the same! A function that assigns a line to any two points -/
    lineBy : Points α → Points α → (Line S)
        -- While Space α defines what a space is, Objects S describes which geometric objects reside in that space
        -- lines is the set of all lines in the space
        -- lineBy is a function stored within the structure, if given two points it returns a set of points
        -- lean does not yet know it is a line, it does not know that the line contains the points, it does not know the line is unique

    -- properties of these definitions
    -- "Through two distinct points in α, there is a line."
    -- axiom stored within the structure
    exists_lineBy : ∀ p q : Points α, p ≠ q → lineBy p q ∈ lines
        -- for any two points p q the set lineBy p q is one of the lines in lines

    -- we state that the line determined by two points p q contains both points, this is axiomatic
    -- first we said a line exists (lineBy) now we say that the two points are actually part of that line
    mem_lineBy_left : ∀ p q : Points α, p ∈ lineBy p q
    mem_lineBy_right : ∀ p q : Points α, q ∈ lineBy p q
    -- "There is at most one line through any two (distinct) points."
    unique_lineBy : ∀ p q : Points α, ∀ l l' : Line S,
      p ≠ q → l ∈ lines → l' ∈ lines → {p, q} ⊆ l.carrier → {p, q} ⊆ l'.carrier → l = l'
          -- take two sets l and l', assume they both declared lines, assume both contain both points, then they are equal
          -- brackets start at (l=l') and then work outwards/backwards.

structure ObjectsWithCoordinate (S : Space α) where
    /- The set of all the lines in our space -/
    lines : Set (LineWithCoordinate S)
    /- The line defined by two points. Uses a junk value if the points are the same! A function that assigns a line to any two points -/

    -- POSTULATE 1
    lineBy : Points α → Points α → (LineWithCoordinate S)
        -- While Space α defines what a space is, Objects S describes which geometric objects reside in that space
        -- lines is the set of all lines in the space
        -- lineBy is a function stored within the structure, if given two points it returns a set of points
        -- lean does not yet know it is a line, it does not know that the line contains the points, it does not know the line is unique

    -- properties of these definitions
    -- "Through two distinct points in α, there is a line."
    -- axiom stored within the structure
    exists_lineBy : ∀ p q : Points α, p ≠ q → lineBy p q ∈ lines
        -- for any two points p q the set lineBy p q is one of the lines in lines

    -- we state that the line determined by two points p q contains both points, this is axiomatic
    -- first we said a line exists (lineBy) now we say that the two points are actually part of that line
    mem_lineBy_left : ∀ p q : Points α, p ∈ (lineBy p q).carrier
    mem_lineBy_right : ∀ p q : Points α, q ∈ (lineBy p q).carrier
    -- "There is at most one line through any two (distinct) points."
    unique_lineBy : ∀ p q : Points α, ∀ l l' : LineWithCoordinate S,
      p ≠ q → l ∈ lines → l' ∈ lines → {p, q} ⊆ l.carrier → {p, q} ⊆ l'.carrier → l = l'
          -- take two sets l and l', assume they both declared lines, assume both contain both points, then they are equal
          -- brackets start at (l=l') and then work outwards/backwards.

    -- second part of POSTULATE 3 : THE RULER POSTULATE
    line_dist : ∀ l ∈ lines, ∀ p q : l.carrier,
      S.dist p q = |l.coordinate p - l.coordinate q|

----------------------------------------------- End of structure Objects ---------------------------------------------------------------------------


namespace ObjectsWithCoordinate
-- opening a namespace called ObjectsWithCoordinate
-- all subsequent definitions will be within this namespace
-- All subsequent definitions are prefixed with Objects
-- we defined the structure Objects and now we want to define lemmas, theorems about Objects... this way they are grouped and confusion can be avoided
-- the functions defined within the structure Objects are projections, to use them you would write Objects.lineBy
-- by opening the namespace we are doing exactly that automatically  (I think??????)
/-
however for o : Objects S
we still need to write o.lineBy p q
lineBy expects an Objects instance as its first argument
-/



variable {S : Space α}
-- declaration of an implicit variable S of type Space α, scoped to the namespace Objects
-- once again the curly brackets make it an implicit argument, lean will try to infer S from context later
-- S : Space α contains at least S.coord : α ≃ (Fin 3 → ℝ)
-- it is introducing a piece of data representing the chosen space structure on α



/-
What the inputs mean:
(o : ObjectsWithCoordinate S) -> o is our axiomatic package, it contains the data (lines, lineBy) and the axioms (exists_lineBy, mem_lineBy_left/right, unique_lineBy) for the Space S
(p q : Point α) gives us two points

The goal is to show that o.lineBy p q and o.lineBy q p are both sets of points (Set α), which are equal as sets
:= by starts the tactic mode for the proof
-/


lemma lineBy_symm (o : ObjectsWithCoordinate S) (p q : Points α) : o.lineBy p q = o.lineBy q p := by
  by_cases h : p = q
        -- split on whether or not p and q are equal
  -- case 1: p=q
  · rw [h]
    -- after rewriting q to p the goal becomes o.lineBy p p = o.lineBy p p which is true by reflexivity
    -- rw [h] typically reduces it immediately
  -- case 2: p ≠ q
  · apply o.unique_lineBy p q _ _ h
        /-
        o.unique_lineBy looks like this:
          ∀ p q, ∀ l l',
          p ≠ q →
          l ∈ o.lines →
          l' ∈ o.lines →
          {p, q} ⊆ l →
          {p, q} ⊆ l' →
          l = l'
        we want to conclude: o.lineBy p q = o.lineBy q p
        we use unique_lineBy with
          l := o.lineBy p q and l' := o.lineBy q p
        that is what the _ _ placeholders are, Lean will fill them with those two sets based on the goal after apply
        after apply we get a list of subgoals
          prove o.lineBy p q ∈ o.lines
          prove o.lineBy q p ∈ o.lines
          prove {p, q} ⊆ o.lineBy p q
          prove {p, q} ⊆ o.lineBy q p
        -/
    · apply o.exists_lineBy
      -- This takes us a step back. We need to show that there exists a line.  We have a theorem that says that for any two distinct points there exists a line containing them both. By applying the theorem we now need to show that p and q are distinct.
      apply h
        -- deals with subgoal one
    · apply o.exists_lineBy
      symm
      apply h
      -- deals with subgoal two
    · have h1 : p ∈ (o.lineBy p q).carrier := by
        apply o.mem_lineBy_left
      have h2 : q ∈ (o.lineBy p q).carrier := by
        apply o.mem_lineBy_right
      exact Set.pair_subset_iff.2 ⟨h1, h2⟩
        -- deals with subgoal three
        -- lesson learnt: ask Gpt if there is a theorem doing what you want before trying to prove it manually
    · have h1 : q ∈ (o.lineBy q p).carrier := by
        apply o.mem_lineBy_left
      have h2 : p ∈ (o.lineBy q p).carrier := by
        apply o.mem_lineBy_right
      exact Set.pair_subset_iff.2 ⟨h2, h1⟩
        -- deals with subgoal four
        -- we are done!

def between {S : Space α} (o : ObjectsWithCoordinate S) (p q r : Points α)  : Prop :=
  p ≠ q ∧ q ≠ r ∧ r ≠ p ∧ q ∈ (o.lineBy p r).carrier ∧ (S.dist p q + S.dist q r = S.dist p r)
    -- p, q, r are three distinct points
    -- q lies on the line defined by p and r
    -- the distance from p to r is the sum of the distances from p to q and from q to r


lemma between_symm (o : ObjectsWithCoordinate S) (p q r : Points α) :
    o.between p q r → o.between r q p := by
  intro h
  cases h with
  | intro h_pq h_rest =>
  -- notation mit | intro erlaubt es, die Bestandteile einer Konjunktion zu extrahieren
    cases h_rest with
    | intro h_qr h_rest2 =>
      cases h_rest2 with
      | intro h_rp h_rest3 =>
        cases h_rest3 with
        | intro h_in_line h_dist_eq =>
          apply And.intro
          symm
          exact h_qr
          apply And.intro
          symm
          exact h_pq
          apply And.intro
          symm
          exact h_rp
          apply And.intro
          rw [lineBy_symm] at h_in_line
          exact h_in_line
          rw [S.dist_symm p q, S.dist_symm q r, S.dist_symm p r] at h_dist_eq
          rw [add_comm] at h_dist_eq
          exact h_dist_eq

lemma not_between (o : ObjectsWithCoordinate S) (p q r : Points α)  (hpqr: o.between p q r) :  ¬ o.between p r q  := by
  intro h
  rw [between] at hpqr
  rw [between] at h
  have h1 : S.dist p q + S.dist q r = S.dist p r := by  exact hpqr.2.2.2.2
  have h2 : S.dist p r + S.dist r q = S.dist p q := by  exact h.2.2.2.2
  rw [← h2] at h1
  rw [S.dist_symm r q] at h1
  have h3 : S.dist q r = 0 := by  linarith
  have h4 : q ≠ r := by  exact hpqr.2.1
  have h5 : S.dist q r > 0 := by  exact S.dist_pos q r h4
  have h6 : ¬ (S.dist q r = 0) := by  linarith
  contradiction

-- thm 2-1.
theorem coordinates_between_points_between (o : ObjectsWithCoordinate S) (p q r : Points α) (l : LineWithCoordinate S) (hl: l ∈ o.lines)
    (hp : p ∈ l.carrier) (hq : q ∈ l.carrier) (hr : r ∈ l.carrier) :
    (l.coordinate) ⟨p, hp⟩ < (l.coordinate) ⟨q, hq⟩ ∧
    (l.coordinate) ⟨q, hq⟩ < (l.coordinate) ⟨r, hr⟩ → o.between p q r := by

    intro h
    -- introducting the hypothesis: l.coordinate ⟨p, hp⟩ < l.coordinate ⟨q, hq⟩ ∧ l.coordinate ⟨q, hq⟩ < l.coordinate ⟨r, hr⟩

    set x := (l.coordinate) ⟨p, hp⟩     -- variables introduced for readability set fixes them, whereas let does not
    set y := (l.coordinate) ⟨q, hq⟩
    set z := (l.coordinate) ⟨r, hr⟩

    have h_xy := h.1                   -- extracting the sub-parts of the conjuction in h
    have h_yz := h.2

    have h_xz : x < z := lt_trans h_xy h_yz       -- showing that x < z if x < y and y < z

    have h_dist_pq : S.dist q p = |y - x| := by   -- distance is the absolute value of the difference of the coordinates
      apply o.line_dist l hl ⟨q, hq⟩ ⟨p, hp⟩
    have h_dist_qr : S.dist r q = |z - y| := by
      apply o.line_dist l hl ⟨r, hr⟩ ⟨q, hq⟩
    have h_dist_pr : S.dist r p = |z - x| := by
      apply o.line_dist l hl ⟨r, hr⟩ ⟨p, hp⟩

    -- show that p ≠ q, q ≠ r, and p ≠ r
    have h_pq_ne : p ≠ q := by
      intro hpq               -- we take p ≠ q and make it into p = q → false
      subst hpq                -- rewrites everything using p = q
      exact lt_irrefl _ h_xy  -- we use that less-than is irreflexive ¬(a < a)

    have h_qr_ne : q ≠ r := by
      intro hqr
      subst hqr
      exact lt_irrefl _ h_yz

    have h_pr_ne : p ≠ r := by
      intro hpr
      subst hpr
      exact lt_irrefl _ h_xz

    -- break down the goal into the different parts needed in the o.between p q r definition
    refine And.intro h_pq_ne ?_   -- we have proved the fist part of the conjunction, and are now taking that out
    refine And.intro h_qr_ne ?_   -- he have proved the second part of the conjunction (first of the rest) and are taking it out
    refine And.intro (Ne.symm h_pr_ne) ?_ -- same as above, just that we have to change p ≠ r to r ≠ p which we do with Ne.symm

    refine And.intro ?_ ?_        -- breaks down the last conjunction and introduces "cases"

    -- first show q ∈ (o.lineBy p r).carrier
    · -- goal: q ∈ (o.lineBy p r).carrier
        -- therefore show that o.lineBy p r = l
      have h_line_pr : o.lineBy p r = l := by
        apply o.unique_lineBy p r (o.lineBy p r) l
          /-
          uses unique_lineBy axiom with two points p r, l:= (o.lineBy p q) and l':=l
          changes goal from o.lineBy p r to list of premises required by unique_lineBy
            1.  p ≠ r
            2.  o.lineBy p r ∈ o.lines
            3. l ∈ o.lines
            4.  {p, r} ⊆ (o.lineBy p r).carrier
            5.  {p, r} ⊆ l.carrier
          -/
        · exact h_pr_ne
          -- we have already proved p ≠ r in h_pr_ne
        · exact o.exists_lineBy p r h_pr_ne
          -- we use o.exists_lineBy to close the second goal, we say the line constructed by lineBy p r is in o.lines, when p ≠ r, for which we provide h_pr_ne as a proof
        · exact hl
          -- shows that l is indeed in o.lines
        · exact Set.pair_subset_iff.2 ⟨o.mem_lineBy_left p r, o.mem_lineBy_right p r⟩
          -- Set.pair_subset_iff is the lemma {a, b} ⊆ s ↔ (a ∈ s ∧ b ∈ s)
          -- .2 means we use the forward direction of it
          -- we need to provide a pair ⟨..., ...⟩ proving membership, which we do by o.mem_lineBy_left/right
        · exact Set.pair_subset_iff.2 ⟨hp, hr⟩
          -- same as above

      -- then show q is on o.lineBy p r
      have hq_on : q ∈ (o.lineBy p r).carrier := by
        simpa [h_line_pr] using hq   -- we replace l in hq with o.lineBy p r and get q ∈ (olineBy p q).carrier
      exact hq_on
      -- close this case

    -- secondly show that the sum works
    · -- goal: S.dist p q + S.dist q r = S.dist p r
      have hpq : S.dist p q = |y - x| := by
        simpa [S.dist_symm] using h_dist_pq
      have hqr : S.dist q r = |z - y| := by
        simpa [S.dist_symm] using h_dist_qr
      have hpr : S.dist p r = |z - x| := by
        simpa [S.dist_symm] using h_dist_pr

      have h_abs_yx : |y - x| = y - x := by
        exact abs_of_pos (sub_pos_of_lt h_xy)
      have h_abs_zy : |z - y| = z - y := by
        exact abs_of_pos (sub_pos_of_lt h_yz)
      have h_abs_zx : |z - x| = z - x := by
        exact abs_of_pos (sub_pos_of_lt h_xz)

      have dist_sum : S.dist p q + S.dist q r = S.dist p r := by
        rw [hpq, hqr, hpr, h_abs_yx, h_abs_zy, h_abs_zx]
        linarith
      exact dist_sum
      -- close the second case
  -- celebrate, we're done! :)


-- does not have an equivalent in the book but does help immensely in the proof of theorem 2.2
lemma coord_eq_iff_point_eq
    (l : LineWithCoordinate S) {a b : Points α}
    (ha : a ∈ l.carrier) (hb : b ∈ l.carrier) :
    l.coordinate ⟨a, ha⟩ = l.coordinate ⟨b, hb⟩ ↔ a = b := by
  constructor           -- show each direction of the iff separately
  · -- (→) injectivity
    intro h           -- let l.coordinate ⟨a, ha⟩ = l.coordinate ⟨b, hb⟩
    have h_ab_line_elements : (⟨a, ha⟩ : {t // t ∈ l.carrier}) = ⟨b, hb⟩ := by
                        -- look at a and b as elements of the subtype of points on the line l
      apply (l.coordinate).injective  -- use that coordinate is injective
      exact h                         -- use the hypothesis
    simpa using congrArg Subtype.val h_ab_line_elements  -- extract the values from the subtype equality to get a = b
  · -- (←) congruence
    intro hab         -- let a = b
    subst hab         -- rewrite b to a in the goal
    rfl               -- goal is now l.coordinate ⟨a, ha⟩ = l.coordinate ⟨a, ha⟩ which is true by reflexivity

-- TODO this might help make the proof of theorem 2.2 cleaner, not sure though
-- not actually used but nifty nonetheless
theorem coordinates_between_points_between_symm (o : ObjectsWithCoordinate S) (p q r : Points α) (l : LineWithCoordinate S) (hl: l ∈ o.lines)
    (hp : p ∈ l.carrier) (hq : q ∈ l.carrier) (hr : r ∈ l.carrier) :
    (l.coordinate) ⟨r, hr⟩ < (l.coordinate) ⟨q, hq⟩ ∧
    (l.coordinate) ⟨q, hq⟩ < (l.coordinate) ⟨p, hp⟩ → o.between p q r := by

    intro h
    have h_rq := h.1
    have h_qp := h.2
    apply between_symm o r q p
    apply coordinates_between_points_between o r q p l hl hr hq hp at h
    exact h




-- thm 2-2.
theorem exists_between (o : ObjectsWithCoordinate S) (p q r : Points α) (hpq: p ≠ q) (hqr: q ≠ r) (hrp: r ≠ p)
  (l : LineWithCoordinate S) (hl: l ∈ o.lines)
  (hp : p ∈ l.carrier) (hq : q ∈ l.carrier) (hr : r ∈ l.carrier):
  o.between p q r ∨ o.between p r q ∨ o.between r p q  := by

    set x := (l.coordinate) ⟨p, hp⟩     -- variables introduced for readability
    set y := (l.coordinate) ⟨q, hq⟩
    set z := (l.coordinate) ⟨r, hr⟩

    have hxy := lt_trichotomy x y       -- linear-order trichotomy on real numbers (x < y) ∨ (x = y) ∨ (x > y)
    cases hxy with
    /- 1. _______ we assume the left side of the disjunction: x < y _________________________________________________-/
    | inl hxy_lt =>
      /-
        inl and inr stand for in-left and in-right
        inl hxy_lt means we prove the left side of the disjunction and call the proof hxy_lt
      -/

        have hyz := lt_trichotomy y z   -- linear order trichotomy on real numbers (y < z) ∨ (y = z) ∨ (y > z)
        cases hyz with

        /- 1.1. _______ we assume the left side of the disjunction: y < z _________________________________________________-/
        | inl hyz_lt =>
            left                        -- we look at the left side of the goal disjunction: o.between p q r
            apply coordinates_between_points_between o p q r l hl hp hq hr
              /-
                replaces goal with the premises of coordinates_between_points_between
                the theorem needs:
                  o : ObjectsWithCoordinate S
                  p q r : Points α
                  l : LineWithCoordinate S
                  hl: l ∈ o.lines
                  hp : p ∈ l.carrier
                  hq : q ∈ l.carrier
                  hr : r ∈ l.carrier
                  and the hypothesis:
                  (l.coordinate) ⟨p, hp⟩ < (l.coordinate) ⟨q, hq⟩ ∧ (l.coordinate) ⟨q, hq⟩ < (l.coordinate) ⟨r, hr⟩
                  which we have as hxy_lt and hyz_lt
              -/
            exact And.intro hxy_lt hyz_lt
              -- And.intro builds proof of A ∧ B from proofs of A and B, we provide the proofs for A and B (hxy_lt and hyz_lt)

        /- 1.2 _______ -- we assume the right side of the disjunction: (y = z) ∨ (y > z) _________________________________________ -/
        | inr hyz_eq_gt =>
            cases hyz_eq_gt with      -- we look at the two different parts of it

            /- 1.2.1 _______ we assume the left side of the disjunction: y = z _________________________________________________-/
            | inl hyz_eq =>
                exfalso               -- we want to prove a contradiction now, so we use exfalso to change the goal to false
                have h_qr_eq : q = r := (coord_eq_iff_point_eq (S:=S) l hq hr).1 (by simpa [y, z] using hyz_eq)
                    /-
                      we introduce a new hypothesis h_qr_eq : q = r
                      we use the previously proved lemma coord_eq_iff_point_eq
                           we need to instantiate that lemma with
                            - space parameter S
                            - line l
                            - points a := q and b := r
                            - proofs that q and r are on the line l: hq and hr
                          it becomes l.coordinate ⟨q, hq⟩ = l.coordinate ⟨r, hr⟩ ↔ q = r
                          we want the left to right direction, so we use .1 to get that direction of the iff
                      we need to provide the needed input
                      we have y = z by hyz_eq, and by definition y = l.coordinate ⟨q, hq⟩ and z = l.coordinate ⟨r, hr⟩
                      simpa [y, z] using hyz_eq rewrites hyz_eq to l.coordinate ⟨q, hq⟩ = l.coordinate ⟨r, hr⟩
                    -/
                exact hqr h_qr_eq    -- we use hqr : q ≠ r and the new hypothesis h_qr_eq : q = r to derive a contradiction

            /- 1.2.2 _______ we assume the right side of the disjunction: y > z _________________________________________________-/
            | inr hyz_gt =>          -- we assume y > z
                right                -- we look at the right side of the goal disjunction: o.between p r q ∨ o.between r p q

                -- we only know x < y and z < y, but not how x and z compare
                have hxz := lt_trichotomy x z   -- linear order trichotomy on real numbers (x < z) ∨ (x = z) ∨ (x > z)
                cases hxz with

                /- 1.2.2.1 _______ we assume the left side of the disjunction: x < z _________________________________________________-/
                | inl hxz_lt =>
                    left              -- we look at the left side of that disjunction: o.between p r q
                    apply coordinates_between_points_between o p r q l hl hp hr hq
                      /-
                        replaces goal with the premises of coordinates_between_points_between
                        the theorem needs:
                          o : ObjectsWithCoordinate S
                          p r q : Points α
                          l : LineWithCoordinate S
                          hl: l ∈ o.lines
                          hp : p ∈ l.carrier
                          hq : q ∈ l.carrier
                          hr : r ∈ l.carrier
                          and the hypothesis:
                          (l.coordinate) ⟨p, hp⟩ < (l.coordinate) ⟨r, hr⟩ ∧ (l.coordinate) ⟨r, hr⟩ < (l.coordinate) ⟨q, hq⟩
                          which we have as hxz_lt and hyz_gt
                      -/
                    exact And.intro hxz_lt hyz_gt
                      -- And.intro builds proof of A ∧ B from proofs of A and B, we provide the proofs for A and B (hxz_lt and hyz_gt)
                /- 1.2.2.2 _______ we assume the right side of the trichotomy: x = z or x > z _________________________________________________-/
                | inr hxz_eq_gt =>
                    cases hxz_eq_gt with
                    /- 1.2.2.2.1 _______________ we assume the left side: x = z _________________________________________________-/
                    | inl hxz_eq =>
                        exfalso
                        have h_pr_eq : p = r := (coord_eq_iff_point_eq (S:=S) l hp hr).1 (by simpa [x, z] using hxz_eq)
                        have h_rp_eq : r = p := Eq.symm h_pr_eq
                        exact hrp h_rp_eq  -- we use hrp : r ≠ p and the new hypothesis h_rp_eq : r = p to derive a contradiction
                    /- 1.2.2.2.2 _______________ we assume the right side: x > z _________________________________________________-/
                    | inr hxz_gt =>
                        right                -- we look at the right side of that disjunction: o.between r p q
                        apply coordinates_between_points_between o r p q l hl hr hp hq
                        exact And.intro hxz_gt hxy_lt
    /- 2. _______ we assume the right side of the disjunction: (x = y) ∨ (x > y) _________________________________________ -/
    | inr hxy_eq_gt =>
        cases hxy_eq_gt with
        /- 2.1 _______ we assume the left side of the disjunction: x = y _________________________________________________-/
        | inl hxy_eq =>
            exfalso
            have h_pq_eq : p = q := (coord_eq_iff_point_eq (S:=S) l hp hq).1 (by simpa [x, y] using hxy_eq)
            exact hpq h_pq_eq    -- we use hpq : p ≠ q and the new hypothesis h_pq_eq : p = q to derive a contradiction
        /- 2.2 _______ we assume the right side of the disjunction: x > y _________________________________________________-/
        | inr hxy_gt =>
            have hyz := lt_trichotomy y z   -- linear order trichotomy on real numbers (y < z) ∨ (y = z) ∨ (y > z)
            cases hyz with
            /- 2.2.1 _______ we assume the left side of the disjunction: y < z _________________________________________________-/
            | inl hyz_lt =>
                right                -- we look at the right side of the goal disjunction: o.between p r q ∨ o.between r p q
                -- we only know x > y and y < z, but not how x and z compare
                have hxz := lt_trichotomy x z   -- linear order trichotomy on real numbers (x < z) ∨ (x = z) ∨ (x > z)
                cases hxz with
                /- 2.2.1.1 _______ we assume the left side of the disjunction: x < z _________________________________________________-/
                | inl hxz_lt =>
                    right            -- we look at the left side of that disjunction: o.between r
                    apply o.between_symm  q p r
                    apply coordinates_between_points_between o q p r l hl hq hp hr
                    exact And.intro hxy_gt hxz_lt
                /- 2.2.1.2 ________ we assume the right side of the disjunction x = z ∨ x > z _________________________________________________-/
                | inr hxz_eq_gt =>
                    cases hxz_eq_gt with
                    /- 2.2.1.2.1 ________ we assume the left side: x = z _________________________________________________-/
                    | inl hxz_eq =>
                        exfalso
                        have h_pr_eq : p = r := (coord_eq_iff_point_eq (S:=S) l hp hr).1 (by simpa [x, z] using hxz_eq)
                        have h_rp_eq : r = p := Eq.symm h_pr_eq
                        exact hrp h_rp_eq    -- we use hrp : r ≠ p and the new hypothesis h_pr_eq : p = r to derive a contradiction
                    /- 2.2.1.2.2 ________ we assume the right side: x > z _________________________________________________-/
                    | inr hxz_gt =>
                        left              -- we look at the left side of that disjunction: o.between r
                        apply o.between_symm  q r p
                        apply coordinates_between_points_between o q r p l hl hq hr hp
                        exact And.intro hyz_lt hxz_gt
            /- 2.2.2 _______ we assume the right side of the disjunction: y = z ∨ y > z _________________________________________________-/
            | inr hyz_eq_gt =>
                cases hyz_eq_gt with
                /- 2.2.2.1 ________ we assume the left side: y = z _________________________________________________-/
                | inl hyz_eq =>
                    exfalso
                    have h_qr_eq : q = r := (coord_eq_iff_point_eq (S:=S) l hq hr).1 (by simpa [y, z] using hyz_eq)
                    exact hqr h_qr_eq    -- we use hqr : q ≠ r and the new hypothesis h_qr_eq : q = r to derive a contradiction
                /- 2.2.2.2 ________ we assume the right side: y > z _________________________________________________-/
                | inr hyz_gt =>
                    left               -- we look at the right side of that disjunction: o.between r p q
                    apply o.between_symm  r q p
                    apply coordinates_between_points_between o r q p l hl hr hq hp
                    exact And.intro hyz_gt hxy_gt






-- thm 2-3.
theorem unique_between  (o : ObjectsWithCoordinate S) (p q r : Points α) (hpq: p ≠ q) (hqr: q ≠ r) (hrp: r ≠ p)
  (l : LineWithCoordinate S) (hl: l ∈ o.lines)
  (hp : p ∈ l.carrier) (hq : q ∈ l.carrier) (hr : r ∈ l.carrier) : (o.between p q r ∨ o.between p r q ∨ o.between r p q) ∧ ¬ (o.between p q r ∧ o.between r p q) ∧ ¬ (o.between p q r ∧ o.between p r q) ∧ ¬ (o.between r p q ∧  o.between p r q):= by
    refine And.intro ?exist ?uniqueness
  -- splitting the goal into existence and uniqueness parts
    · have h_exist := exists_between o p q r hpq hqr hrp l hl hp hq hr
      exact h_exist

    ·  -- proving uniqueness
      refine And.intro ?_ ?_
      -- proving ¬ (o.between p q r ∧ o.between r p q)
      · intro h_between_both_1
        cases h_between_both_1 with
        | intro h_between_pqr h_between_rpq =>
          have h_contra := not_between o r p q h_between_rpq
          apply between_symm o p q r at h_between_pqr
          exact h_contra h_between_pqr
      -- proving ¬ (o.between p q r ∧ o.between p r q)
      · refine And.intro ?_ ?_
        -- proving ¬ (o.between p q r ∧ o.between p r q)
        · intro h_between_both_2
          cases h_between_both_2 with
          | intro h_between_pqr h_between_prq =>
            have h_contra := not_between o p r q h_between_prq
            exact h_contra h_between_pqr
        -- proving ¬ (o.between r p q ∧  o.between p r q)
        · intro h_between_both_3
          cases h_between_both_3 with
          | intro h_between_rpq h_between_prq =>
            apply between_symm o r p q at h_between_rpq
            apply between_symm o p r q at h_between_prq
            have h_contra := not_between o q r p h_between_prq
            exact h_contra h_between_rpq





end ObjectsWithCoordinate
-- end of namespace ObjectsWithCoordinate
