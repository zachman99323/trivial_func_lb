import Mathlib

set_option linter.unusedVariables false

open Set
open scoped Classical
open Finset BigOperators

variable {X : Type*}
variable {F : Set (Set X)}
def union_closed (F : Set (Set X)) := (∀A, ∀B, (A∈F ∧ B∈F → A∪B ∈ F))

--trivial lemma about sets: if C is nonempty and doesn't equal {x}, then there's some y≠x in C
lemma small_lemma_about_sets.{u1} {Y : Type u1} (x : Y) (C : Set Y)
(hCnonemp: C.Nonempty) (hCnex: C ≠ {x}) : ∃ y : Y, y ≠ x ∧ y ∈ C := by
  by_cases hxinC: x ∈ C; swap
  . rcases hCnonemp with ⟨y,hy⟩; use y; apply And.intro; swap; exact hy
    contrapose! hxinC; rw[← hxinC]; exact hy
  . contrapose! hCnex; apply Set.Subset.antisymm; swap; simp only [Set.singleton_subset_iff]; exact hxinC
    intro y hyinC; have hneimp := hCnex y; rw[not_imp_not] at hneimp; exact hneimp hyinC

--for any subfamily G, the union of all the sets in G is in F
theorem UG_in_F (hFuc: union_closed F) (G : Set (Set X)) (hGnonemp: ∃A, A ∈ G) (hGsubF : G ⊆ F) (hGfin: G.Finite):
⋃₀G ∈ F := by
  suffices: ∀(n : ℕ), ∀(G : Set (Set X)), (G.ncard = n) ∧ (∃A, A ∈ G) ∧ G ⊆ F ∧ G.Finite → ⋃₀ G ∈ F
  . exact this G.ncard G ⟨rfl, hGnonemp, hGsubF, hGfin⟩
  clear hGnonemp; clear hGsubF; clear hGfin; clear G
  intro n; induction' n with n hind

  --case n=0
  intro G ⟨hG1,hG2,hG3,hG4⟩
  apply False.elim; aesop

  --induction step
  intro G ⟨hGncard,hGnonemp,hGsubF,hGfin⟩; rcases hGnonemp with ⟨A0,hA0inG⟩
  by_cases hsingleton: G = {A0}; rw[hsingleton]; rw [sUnion_singleton]; exact hGsubF hA0inG
  let G1 := G\{A0}
  have hGdecomp: G = G1 ∪ {A0} := by dsimp[G1]; aesop
  have hG1subG : G1 ⊆ G := by exact diff_subset
  have hG1: G1.ncard = n ∧ (∃A, A ∈ G1) ∧ (G1 ⊆ F) ∧ (G1.Finite) := by
    apply And.intro; dsimp[G1]; swap; apply And.intro; swap; apply And.intro
    apply subset_trans hG1subG hGsubF; exact Finite.subset hGfin hG1subG; swap
    suffices: (G\{A0}).ncard+1 = n+1
    . apply Nat.add_right_cancel this
    rw[← hGncard]; exact ncard_diff_singleton_add_one hA0inG hGfin
    have hnear := small_lemma_about_sets A0 G ?_ hsingleton; rcases hnear with ⟨A,hA⟩
    use A; dsimp[G1]; simp only [mem_diff, mem_singleton_iff]; exact ⟨hA.2,hA.1⟩; use A0
  have hnear := hind G1 hG1
  rw[hGdecomp]; simp only [union_singleton, sUnion_insert]; exact hFuc _ _ ⟨(hGsubF hA0inG),hnear⟩

--a hitting set is a set S ⊆ X that intersects every nonempty set in F
def hitting_set (S : Set X) (F : Set (Set X)) := ∀(A : Set X), ((A ∈ F ∧ A.Nonempty) → (∃(x : X), ((x ∈ S) ∧ (x ∈ A))))

--any family has a hitting set
theorem hitting_sets_exist : ∃(S : Set X), hitting_set S F := by
  use Set.univ
  dsimp[hitting_set]; intro A hA; have hA2 := hA.2; rcases hA2 with ⟨a,ha⟩
  use a; apply And.intro; swap; exact ha; exact trivial

--any family has a minimal set w.r.t. inclusion
theorem min_set_exists (hfinX: Finite X) (G : Set (Set X)) (hGnonemp: G.Nonempty) : ∃(S : Set X), (S ∈ G) ∧ (∀(T : Set X), (T ∈ G ∧ T⊆ S → T=S)) := by
  have hGfin : G.Finite := toFinite G
  let f : Set X → Set X := fun A ↦ A
  rcases Set.Finite.exists_minimal_wrt f G hGfin hGnonemp with ⟨S,hS⟩
  have hS1 := hS.1; have hS2 := hS.2; clear hS; use S
  apply And.intro; exact hS1; intro T hT; have hT0 := hS2 T hT.1; dsimp[f] at hT0; aesop

--a minimal hitting set is a hitting set that is minimal w.r.t. inclusion (amongst hitting sets)
def minimal_hitting_set (S : Set X) (F : Set (Set X)) := (hitting_set S F) ∧ (∀(T : Set X), (T ⊆ S ∧ ¬(T = S)) → ¬(hitting_set T F))

--any family has a minimal hitting set (minimal w.r.t. inclusion)
theorem minimal_hitting_sets_exist (hfinX: Finite X) (F : Set (Set X)) : ∃(S : Set X), minimal_hitting_set S F := by
  let G : Set (Set X) := {S : Set X | hitting_set S F}
  have hGnonemp : G.Nonempty := hitting_sets_exist
  rcases min_set_exists hfinX G hGnonemp with ⟨S,hS1,hS2⟩; use S
  dsimp[minimal_hitting_set]; apply And.intro
  . dsimp[hitting_set]; intro A ⟨hA1,hA2⟩; aesop
  . intro T ⟨hT1,hT2⟩; contrapose! hT2; aesop

--the key property of a minimal hitting set S: for any x in S, there's some set in the family interesecting S only at x
theorem key_property_of_mhs (S : Set X) (hSmhs: minimal_hitting_set S F) : ∀(x : X), x ∈ S → ( ∃(A : Set X), (A ∈ F ∧ A∩S = {x})) := by
  intro x hx
  contrapose! hSmhs; dsimp[minimal_hitting_set]; push_neg; intro hShs; use S\{x}; apply And.intro;
  . apply And.intro; intro y hy; rw[mem_diff] at hy; exact hy.1
    have hxS : x ∉ S\{x} := by
      rw[mem_diff]; push_neg; intro h0; rfl
    contrapose! hxS; rw[hxS]; exact hx
  . dsimp[hitting_set]; intro A ⟨hA1,hA2⟩; have hSmhsA := hSmhs A hA1; dsimp[hitting_set] at hShs
    have hASnonemp : (A∩S).Nonempty := by
      have hShsA := hShs A ⟨hA1,hA2⟩; rcases hShsA with ⟨y,hy⟩; use y; exact ⟨hy.2,hy.1⟩
    rcases small_lemma_about_sets x (A∩S) hASnonemp hSmhsA with ⟨y,hy1,hy2⟩
    use y; apply And.intro; rw[mem_diff]; simp only [mem_singleton_iff]
    apply And.intro; exact hy2.2; exact hy1; exact hy2.1

--there's a bijection from a finite set A to Fin (A.ncard)
theorem ncard_equiv_to_bij (A : Set X) (hAfin: A.Finite) (k : ℕ) (hk: k = A.ncard) : ∃ g : A → Fin k, g.Bijective := by
  --use finite hypothesis to extract bijection from A to some Fin n. use theorem already in Lean to show this means n=k
  have hfinA : Finite A := hAfin; rw[finite_iff_exists_equiv_fin] at hfinA
  rcases hfinA with ⟨n,phi1,phi2,hleftinv,hrightinv⟩
  suffices hneqk: k=n
  . subst hneqk; use phi1; apply Function.bijective_iff_has_inverse.mpr; use phi2

  let f : (i : ℕ) → i < n → X := fun i ↦ (fun h ↦ phi2 ⟨i,h⟩)
  have hfsurj : ∀a ∈ A, ∃i, ∃(hin : i < n), f i hin = a := by
    intro a ha; use (phi1 ⟨a,ha⟩).1; use (phi1 ⟨a,ha⟩).2; dsimp[f]
    have hleftinva := hleftinv ⟨a,ha⟩; rw[hleftinva]
  have hfcodomain : ∀(i : ℕ) (hin : i < n), f i hin ∈ A := by
    intro i hi; dsimp[f]; exact Subtype.coe_prop (phi2 ⟨i,hi⟩)
  have hfinj : ∀(i j : ℕ) (hin : i < n) (hjn : j < n), f i hin = f j hjn → i = j := by
    intro i j hin hjn hfij; dsimp[f] at hfij
    have hfij_fixed : phi2 ⟨i,hin⟩ = phi2 ⟨j,hjn⟩ := SetCoe.ext hfij
    have hphi1phi2 : phi1 (phi2 ⟨i,hin⟩) = phi1 (phi2 ⟨j,hjn⟩) := by rw[hfij_fixed]
    rw[hrightinv ⟨i,hin⟩] at hphi1phi2; rw[hrightinv ⟨j,hjn⟩] at hphi1phi2
    exact Fin.mk.inj_iff.mp hphi1phi2
  have hnear_conc := Set.ncard_eq_of_bijective f hfsurj hfcodomain hfinj
  rw[← hnear_conc]; exact hk

--show {T | T ⊆ S} = {T1 | T1 ⊆ Finite.toFinset S}
lemma subsets_of_finset (S : Set X) (hSfin: S.Finite):
{T : Set X | T ⊆ S}.ncard = {T : Finset X | T ⊆ (Finite.toFinset hSfin)}.ncard := by
  let f : Set X → Finset X := fun T ↦
    if hTsubS : T ⊆ S then Finite.toFinset (Finite.subset hSfin hTsubS)
    else ∅
  have hnear := @Set.ncard_image_of_injOn (Set X) (Finset X) {T : Set X | T ⊆ S} f ?_
  rw[← hnear]; congr; ext T1; apply Iff.intro; intro hT1; simp only [Set.mem_image, mem_setOf_eq] at hT1
  rcases hT1 with ⟨T,hT₁,hT₂⟩; simp only [Finite.subset_toFinset, mem_setOf_eq]; dsimp[f] at hT₂
  simp only [hT₁, ↓reduceDite] at hT₂; rw[← hT₂]; simp only [Finite.coe_toFinset]; exact hT₁
  intro hT1; simp only [Finite.subset_toFinset, mem_setOf_eq] at hT1
  simp only [Set.mem_image,mem_setOf_eq]; use Finset.toSet T1; use hT1; dsimp[f]; simp only [hT1]
  simp only [↓reduceDite, toFinite_toFinset, toFinset_coe]

  --show f is injective on {T : Set X | T ⊆ S}
  intro T1 hT1 T2 hT2 hf12; rw[mem_setOf] at hT1; rw[mem_setOf] at hT2; dsimp[f] at hf12
  simp only [hT1,hT2,↓reduceDite, Finite.toFinset_inj] at hf12; exact hf12

--size of powerset of S is 2^(S.ncard)
theorem size_of_subsets (S : Set X) (hSfin: S.Finite): ({T : Set X | T ⊆ S}).ncard = 2^(S.ncard) := by
  let S1 := Finite.toFinset hSfin; have hS1powcard := Finset.card_powerset S1
  have hncardseq : S.ncard = S1.card := ncard_eq_toFinset_card S hSfin
  rw[hncardseq]; rw[← hS1powcard]
  have hTSfin : {T : Set X | T ⊆ S}.Finite := Finite.finite_subsets hSfin
  suffices: {T : Set X | T ⊆ S}.ncard = {T : Finset X | T ⊆ S1}.ncard
  . rw[this]; let G := Finset.toSet S1.powerset
    have hGncard : G.ncard = S1.powerset.card := ncard_coe_Finset S1.powerset
    rw[← hGncard]; dsimp[G]; congr; simp only [coe_powerset]; rfl
  exact subsets_of_finset S hSfin

--if S is a minimal hitting set for a UC family F, then 2^(S.ncard)-1 ≤ F.ncard
theorem lb_size_mhs_in_uc_fam (S : Set X) (hFinx: Finite X) (hFfin: F.Finite)
(hucF: union_closed F) (hmhs_S: minimal_hitting_set S F) : 2 ^ (S.ncard)-1 ≤ F.ncard := by
  simp only [tsub_le_iff_right]
  let A₀ : Set X := ∅
  let H₀ : Set (Set X) := {A₀}
  let G : Set (Set X) := F ∪ H₀
  have hGncard : G.ncard ≤ F.ncard+1 := by
    dsimp[G]; apply le_trans (ncard_union_le F H₀) ?_; gcongr
    rw[ncard_eq_one.mpr]; use A₀
  apply le_trans ?_ hGncard; rw[← size_of_subsets S (toFinite S)]

  let fpart (T : Set X) (hTS : T ⊆ S) : X → Set X := fun x ↦
    if hxT: x ∈ T then ((key_property_of_mhs S hmhs_S) x (hTS hxT)).choose
    else ∅
  let f : Set X → Set X := fun T ↦
    if hTS: T ⊆ S then ⋃₀ {fpart T hTS x | x ∈ T}
    else ∅
  apply Set.ncard_le_ncard_of_injOn f ?_ ?_ (toFinite G)

  --show f maps {T | T ⊆ S} into G
  intro T hTsubS; rw[mem_setOf] at hTsubS; dsimp[f]; simp only [hTsubS, ↓reduceDite]
  by_cases hTemp: T = ∅
  . suffices: {x | ∃ x_1 ∈ T, (fpart T hTsubS) x_1 = x} = ∅
    . rw[this]; simp only [sUnion_empty]; dsimp[G]; right; dsimp[H₀]; simp only [mem_singleton_iff]
    contrapose! hTemp; rcases hTemp with ⟨x,hx⟩; rw[mem_setOf] at hx; rcases hx with ⟨x1,hx1⟩
    use x1; exact hx1.1
  . dsimp[G]; left; push_neg at hTemp; rcases hTemp with ⟨x0,hx0inT⟩
    have hsubF : {x | ∃ x_1 ∈ T, fpart T hTsubS x_1 = x} ⊆ F := by
      intro A hA; rw[mem_setOf] at hA; rcases hA with ⟨x,hx1,hx2⟩
      dsimp[fpart] at hx2; simp only [hx1,↓reduceDite] at hx2; rw[← hx2]
      exact (((key_property_of_mhs S hmhs_S) x (hTsubS hx1)).choose_spec).1
    apply UG_in_F hucF {x | ∃ x_1 ∈ T, fpart T hTsubS x_1 = x} ?_ hsubF (Finite.subset hFfin hsubF)
    --show family is nonempty
    use fpart T hTsubS x0; rw[mem_setOf_eq]; use x0

  --show f is injective on {T | T ⊆ S}
  have hfTcapS (T : Set X) (hTsubS : T ⊆ S) : (f T) ∩ S = T := by
    ext x; apply Iff.intro
    . intro ⟨hx1,hx2⟩; dsimp[f] at hx1
      simp only [hTsubS,↓reduceDite,mem_sUnion, mem_setOf_eq, exists_exists_and_eq_and] at hx1
      rcases hx1 with ⟨a,ha1,ha2⟩; dsimp[fpart] at ha2; simp only [ha1,↓reduceDite] at ha2
      have hAprop := ((key_property_of_mhs S hmhs_S) a (hTsubS ha1)).choose_spec
      let A := ((key_property_of_mhs S hmhs_S) a (hTsubS ha1)).choose
      suffices: x ∈ A ∩ S
      . rw[hAprop.2] at this; simp only [mem_singleton_iff] at this; rw[this]; exact ha1
      use ha2
    . intro hxT; apply And.intro; swap; exact hTsubS hxT; dsimp[f]
      simp only [hTsubS, ↓reduceDite,mem_sUnion, mem_setOf_eq,exists_exists_and_eq_and]
      use x; use hxT; dsimp[fpart]; simp only [hxT,↓reduceDite]
      have hAprop := ((key_property_of_mhs S hmhs_S) x (hTsubS hxT)).choose_spec
      set A := ((key_property_of_mhs S hmhs_S) x (hTsubS hxT)).choose
      suffices: x ∈ A ∩ S
      . exact Set.mem_of_mem_inter_left this
      rw[hAprop.2]; rfl
  intro T1 hT1 T2 hT2 hf12; rw[mem_setOf] at hT1; rw[mem_setOf] at hT2
  calc
    T1 = f T1 ∩ S := Eq.symm (hfTcapS T1 hT1)
    _ = f T2 ∩ S := by rw[hf12]
    _ = T2 := hfTcapS T2 hT2

--if S is a hitting set, then sum_{x in S} #{A ∈ F : x ∈ A} ≥ F.ncard-1
theorem double_counting_arg (S1 : Finset X) (F : Set (Set X)) (hhsS : hitting_set (Finset.toSet S1) F)
(hFfin: F.Finite) (hAfin: ∀A : Set X, A.Finite):
∑ x ∈ S1, {A : Set X | A ∈ F ∧  x ∈ Finite.toFinset (hAfin A) }.ncard ≥ F.ncard - 1 := by
  let ind : Prop → ℕ := fun P ↦
    if P then 1
    else 0
  let F1 := Finite.toFinset hFfin
  let A₀ : Set X := ∅
  let H₀ : Finset (Set X) := {A₀}
  let F1nonempty := F1 \ H₀

  calc
    ∑ x ∈ S1, {A : Set X | A ∈ F ∧  x ∈ Finite.toFinset (hAfin A) }.ncard = ∑ x ∈ S1, ∑ A ∈ F1, ind (x ∈ A) := by
      rcongr x; simp only [Finite.mem_toFinset]
      set G := {A : Set X | A ∈ F ∧ x ∈ A}
      have hGfin: G.Finite := Finite.sep hFfin fun a ↦ x ∈ a
      set G1 := Finite.toFinset hGfin
      have hG1card : G1.card = G.ncard := by exact Eq.symm (ncard_eq_toFinset_card G hGfin)
      rw[← hG1card]; rw[card_eq_sum_ones G1]
      have hind_eq_1 : ∀A ∈ G1, ind (x ∈ A) = 1 := by
        intro A hA; dsimp[G1] at hA; simp only [Finite.mem_toFinset] at hA; dsimp[G] at hA; dsimp[ind]
        simp only [hA.2,↓reduceIte]
      rw[← sum_congr rfl hind_eq_1]; apply Finset.sum_subset ?_ ?_
      dsimp[G1, F1]; simp only [Finite.subset_toFinset, Finite.coe_toFinset]; exact sep_subset F fun x_1 ↦ x ∈ x_1
      intro A hAinF1 hAnotinG1; dsimp[ind]; simp only [ite_eq_right_iff, one_ne_zero, imp_false]
      contrapose! hAnotinG1; dsimp[G1]; simp only [Finite.mem_toFinset]; dsimp[G]; apply And.intro
      exact (Finite.mem_toFinset hFfin).mp hAinF1; exact hAnotinG1
    _ = ∑ A ∈ F1, ∑ x ∈ S1, ind (x ∈ A) := sum_comm
    _ ≥ ∑ A ∈ F1nonempty, ∑ x ∈ S1, ind (x ∈ A) := by
      have hF1nonsubF1 : F1nonempty ⊆ F1 := by
        dsimp[F1nonempty]; apply Finset.sdiff_subset
      exact sum_le_sum_of_ne_zero fun x a a_1 ↦ hF1nonsubF1 a
    _ ≥ ∑ A ∈ F1nonempty, 1 := by
      gcongr with A hA
      suffices: ∑ x ∈ S1, ind (x ∈ A) > 0
      . exact this
      apply Finset.sum_pos'; intro i hi; exact Nat.zero_le (ind (i ∈ A))
      dsimp[hitting_set] at hhsS; dsimp[F1nonempty] at hA; simp only [mem_sdiff] at hA
      have hnear := hhsS A ⟨?_,?_⟩
      rcases hnear with ⟨i,hi1,hi2⟩; use i; use hi1; dsimp[ind]; simp only [hi2,↓reduceIte, zero_lt_one]
      . dsimp[F1,H₀,A₀] at hA; simp only [Finite.mem_toFinset] at hA; exact hA.1
      . have hnear := hA.2; contrapose! hnear; rw[hnear]; exact Finset.mem_singleton.mpr rfl
    _ = F1nonempty.card := Eq.symm (card_eq_sum_ones F1nonempty)
    _ = (F1 \ H₀).card := by dsimp[F1nonempty]
    _ ≥ F1.card - 1 := by
      suffices: H₀.card = 1
      . rw[← this]; exact le_card_sdiff H₀ F1
      dsimp[H₀,A₀]; rfl
    _ = F.ncard - 1 := by
      dsimp[F1]; congr; symm; exact ncard_eq_toFinset_card F hFfin

--if S is a hitting set, then ∃x ∈ S, {A ∈ F | x ∈ A}.ncard ≥ ((Nat.sub F.ncard 1) : ℝ)/(S.ncard : ℝ)
theorem abundance_in_hs (S : Set X) (x0 : X) (hx0inS : x0 ∈ S) (hXfin: Finite X) (hFfin: F.Finite) (hFgt2: F.ncard > 2)
(hhsS: hitting_set S F) : ∃x ∈ S, {A ∈ F | x ∈ A}.ncard ≥ ((Nat.sub F.ncard 1) : ℝ)/(S.ncard : ℝ) := by

  have basic_lemma_nat_reals (a b c : ℕ) (hbpos : b > 0) : a * b ≥ c → (a : ℝ) ≥ (c : ℝ)/(b : ℝ) := by
    intro h; apply (div_le_iff ?_).mpr ?_; exact Nat.cast_pos.mpr hbpos; norm_cast

  suffices: ∃ x ∈ S, ({A ∈ F | x ∈ A}.ncard)*(S.ncard) ≥ F.ncard-1
  . rcases this with ⟨x,hx1,hx2⟩; use x; use hx1; apply basic_lemma_nat_reals _ _ _ ?_ hx2
    apply (ncard_pos ?_).mpr ?_; exact toFinite S; use x

  set S1 := Finite.toFinset (toFinite S)
  have h_hs_fixed : hitting_set (↑ S1) F := by dsimp[S1]; simp only [Finite.coe_toFinset]; exact hhsS
  have hAfins : ∀(A : Set X), A.Finite := by intro A; exact toFinite A
  have hdoublecounting := double_counting_arg S1 F h_hs_fixed hFfin hAfins
  contrapose! hdoublecounting

  suffices: (∑ x ∈ S1, {A | A ∈ F ∧ x ∈ Finite.toFinset (hAfins A)}.ncard)*(S.ncard) < (F.ncard - 1)*(S.ncard)
  . exact Nat.lt_of_mul_lt_mul_right this
  have hlt_fixed: ∀x ∈ S1, {A | A ∈ F ∧ x ∈ (hAfins A).toFinset}.ncard * S.ncard < F.ncard - 1 := by
    intro x hx
    have hxinS : x ∈ S := by exact (Finite.mem_toFinset (hAfins S)).mp hx
    have hnear := hdoublecounting x hxinS; simp only [Finite.mem_toFinset, gt_iff_lt]; exact hnear

  calc
  (∑ x ∈ S1, {A | A ∈ F ∧ x ∈ (hAfins A).toFinset}.ncard)*S.ncard
    = ∑ x ∈ S1, ({A | A ∈ F ∧ x ∈ (hAfins A).toFinset}.ncard)*(S.ncard) := by apply sum_mul
    _ < ∑ x ∈ S1, (F.ncard-1) := by
      gcongr with x hx; use x0; exact (Finite.mem_toFinset (toFinite S)).mpr hx0inS; exact hlt_fixed x hx
    _ = (F.ncard-1)*(S1.card) := by
      rw[mul_comm]; apply sum_const
    _ = (F.ncard-1)*(S.ncard) := by congr; exact Eq.symm (ncard_eq_toFinset_card S (toFinite S))

--for any UC F, there is some x in at least c/log|F| proportion of the sets of F
theorem trivial_func_lb (hucF : union_closed F) (hXfin : Finite X) (hFgt2: F.ncard > 2)
(x0 : X) (A : Set X) (hAnonempty : A.Nonempty) (hAF : A ∈ F):
∃(x : X), {A ∈ F | x ∈ A}.ncard ≥ ((Nat.sub F.ncard 1) : ℝ)/(Nat.log 2 (F.ncard+1) : ℝ) := by
  have hmhs := minimal_hitting_sets_exist hXfin F; rcases hmhs with ⟨S,hS⟩; have hS1 := hS.1; have hS2 := hS.2
  have hSnonempty : S.Nonempty := by
    dsimp[hitting_set] at hS1; have hS1A := hS1 A ⟨hAF,hAnonempty⟩; rcases hS1A with ⟨a,ha1,ha2⟩; use a
  rcases hSnonempty with ⟨xS,hxS⟩
  have hFfinite : F.Finite := toFinite F
  have habundant := abundance_in_hs S xS hxS hXfin hFfinite hFgt2 hS1
  rcases habundant with ⟨x,hx1,hx2⟩; use x
  suffices: (Nat.sub F.ncard 1 : ℝ) / (S.ncard : ℝ) ≥ (Nat.sub F.ncard 1 : ℝ) / (Nat.log 2 (F.ncard + 1) : ℝ)
  . apply ge_trans hx2 this
  suffices: S.ncard ≤ Nat.log 2 (F.ncard+1)
  . refine div_le_div_of_nonneg_left ?_ ?_ ?_; exact Nat.cast_nonneg (F.ncard.sub 1)
    simp only [Nat.cast_pos]; apply (ncard_pos ?_).mpr; use xS; exact toFinite S; norm_cast
  have hboundS := lb_size_mhs_in_uc_fam S hXfin hFfinite hucF hS
  simp only [tsub_le_iff_right] at hboundS; refine Nat.le_log_of_pow_le ?h.hb hboundS; exact Nat.one_lt_two
