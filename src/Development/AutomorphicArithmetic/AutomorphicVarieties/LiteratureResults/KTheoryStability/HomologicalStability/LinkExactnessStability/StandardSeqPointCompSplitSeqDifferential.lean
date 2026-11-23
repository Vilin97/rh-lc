module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.FaceStdSeqGLConjugateCommutingStab
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsFreeResolutionShortExact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyLongExactMapsNaturalOfRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ProjectiveRepGroupHomologyPosVanishes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Lemma
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.InnerAutActsTriviallyGroupHomology

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

def conjActHom {k G : Type} [CommRing k] [Group G] (g : G) (A : Rep k G) :
    A ⟶ Rep.res (MulAut.conj g).toMonoidHom A :=
  Rep.ofHom ⟨A.ρ g, fun h => LinearMap.ext fun a => by
    change A.ρ g (A.ρ h a) = A.ρ (g * h * g⁻¹) (A.ρ g a)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]⟩

theorem conjActHom_hom_apply {k G : Type} [CommRing k] [Group G] (g : G) (A : Rep k G) (a : A) :
    (conjActHom g A).hom a = A.ρ g a := rfl

theorem conj_map_eq_id_zero (k G : Type) [CommRing k] [Group G] (g : G) (A : Rep k G)
    (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A) (hu : ∀ a, u.hom a = A.ρ g a) :
    groupHomology.map (MulAut.conj g).toMonoidHom u 0 = 𝟙 _ := by
  rw [← cancel_epi (groupHomology.H0π A), groupHomology.H0π_comp_map, Category.comp_id]
  ext a
  have hv : (groupHomology.H0π A).hom (A.ρ g a) = (groupHomology.H0π A).hom a := by
    rw [← groupHomology.coinvariantsMk_comp_H0Iso_inv]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    congr 1
    exact Representation.Coinvariants.mk_self_apply _ _ _
  rw [← hv, ← hu]
  rfl

theorem conj_map_eq_id : ∀ (k G : Type) [CommRing k] [Group G] (g : G) (n : ℕ) (A : Rep k G)
    (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A), (∀ a, u.hom a = A.ρ g a) →
    groupHomology.map (MulAut.conj g).toMonoidHom u n = 𝟙 _ := by
  intro k G _ _ g n
  induction n with
  | zero => exact conj_map_eq_id_zero k G g
  | succ n ih =>
    intro A u hu
    obtain ⟨ι, K, i, e, h, hS⟩ := exists_free_shortExact k G A
    have hP : IsZero (groupHomology (Rep.free k G ι) (n + 1)) :=
      GlobalTheory.T.projective_rep_groupHomology_pos_vanishes k G (Rep.free k G ι) inferInstance n
    have hmono := groupHomology.mono_δ_of_isZero hS n hP
    have hnat := (GlobalTheory.T.groupHomology_longExact_maps_natural_of_res k G G (MulAut.conj g).toMonoidHom _ _ hS hS
      (conjActHom g K) (conjActHom g (Rep.free k G ι)) u
      (fun a => by
        change (Rep.free k G ι).ρ g (i.hom a) = i.hom (K.ρ g a)
        exact (Rep.hom_comm_apply i g a).symm)
      (fun a => by
        change u.hom (e.hom a) = e.hom ((Rep.free k G ι).ρ g a)
        rw [hu]
        exact (Rep.hom_comm_apply e g a).symm) n).1
    rw [ih K (conjActHom g K) (fun _ => rfl), Category.comp_id] at hnat
    rw [← cancel_mono (groupHomology.δ hS (n + 1) n rfl), Category.id_comp]
    exact hnat.symm

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.innerAut_acts_trivially_groupHomology : ∀ (k G : Type) [CommRing k] [Group G] (g : G) (n : ℕ) (A : Rep k G) (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A), (∀ a, u.hom a = A.ρ g a) → groupHomology.map (MulAut.conj g).toMonoidHom u n = 𝟙 _ := by
  first
  | exact @GlobalTheory.HomStab.conj_map_eq_id
  | exact @GlobalTheory.HomStab.conj_map_eq_id_zero
  | exact @GlobalTheory.HomStab.conjActHom_hom_apply
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyMapEqOfInnerConj

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.ConjMap

noncomputable def actHom {k G : Type} [CommRing k] [Group G] (B : Rep k G) (g : G) :
    B ⟶ Rep.res (MulAut.conj g).toMonoidHom B :=
  Rep.ofHom (X := B.V) (Y := B.V) (ρ := B.ρ) (σ := (Rep.res (MulAut.conj g).toMonoidHom B).ρ)
    ⟨B.ρ g, fun h => by ext x; simp [Rep.res]⟩

lemma actHom_apply {k G : Type} [CommRing k] [Group G] (B : Rep k G) (g : G) (x : B) :
    (actHom B g).hom x = B.ρ g x := rfl

end GlobalTheory.HomStab.ConjMap

open GlobalTheory.HomStab.ConjMap in
theorem GlobalTheory.HomStab.groupHomology_map_conj : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (A : Rep k H) (B : Rep k G) (f₁ f₂ : H →* G) (u₁ : A ⟶ Rep.res f₁ B) (u₂ : A ⟶ Rep.res f₂ B) (g : G), (∀ h, f₂ h = g * f₁ h * g⁻¹) → (∀ a, u₂.hom a = B.ρ g (u₁.hom a)) → ∀ n : ℕ, groupHomology.map f₂ u₂ n = groupHomology.map f₁ u₁ n := by
  intro k G H _ _ _ A B f₁ f₂ u₁ u₂ g hf hu n
  have hf' : f₂ = (MulAut.conj g).toMonoidHom.comp f₁ := by
    ext h; simp [hf h]
  have e : groupHomology.map f₂ u₂ n =
      groupHomology.map ((MulAut.conj g).toMonoidHom.comp f₁)
        (u₁ ≫ (Rep.resFunctor f₁).map (actHom B g)) n := by
    apply groupHomology.map_congr hf'
    ext a
    simp [hu a, actHom_apply]
    rfl
  rw [e, groupHomology.map_comp, GlobalTheory.T.innerAut_acts_trivially_groupHomology k G g n B (actHom B g) (fun a => rfl),
    Category.comp_id]

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.HMapSumZsmulAdd

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem chainsMap_id_add {k G : Type} [CommRing k] [Group G] {A B : Rep k G} (f g : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id G) (f + g) =
      groupHomology.chainsMap (MonoidHom.id G) f + groupHomology.chainsMap (MonoidHom.id G) g := by
  ext n : 1
  apply groupHomology.inhomogeneousChains.ext
  intro x
  ext a : 2
  simp only [groupHomology.chainsMap_f_single, HomologicalComplex.add_f_apply]
  simp [groupHomology.chainsMap_f_single]
  rw [← Finsupp.single_add]
  rfl

theorem hMap_add {k G : Type} [CommRing k] [Group G] {A B : Rep k G} (f g : A ⟶ B) (n : ℕ) :
    hMap (f + g) n = hMap f n + hMap g n := by
  unfold hMap groupHomology.map
  rw [chainsMap_id_add, HomologicalComplex.homologyMap_add]

noncomputable def hMapHom {k G : Type} [CommRing k] [Group G] (A B : Rep k G) (n : ℕ) :
    (A ⟶ B) →+ (groupHomology A n ⟶ groupHomology B n) :=
  AddMonoidHom.mk' (fun f => hMap f n) fun f g => hMap_add f g n

theorem hMap_additive : ∀ (k G : Type) [CommRing k] [Group G] (A B : Rep k G) (n : ℕ), (∀ f g : A ⟶ B, hMap (f + g) n = hMap f n + hMap g n) ∧ hMap (0 : A ⟶ B) n = 0 ∧ (∀ (m : ℤ) (f : A ⟶ B), hMap (m • f) n = m • hMap f n) ∧ ∀ (ι : Type) (T : Finset ι) (f : ι → (A ⟶ B)), hMap (∑ i ∈ T, f i) n = ∑ i ∈ T, hMap (f i) n := by
  intro k G _ _ A B n
  refine ⟨fun f g => hMap_add f g n, ?_, ?_, ?_⟩
  · exact map_zero (hMapHom A B n)
  · intro m f
    exact map_zsmul (hMapHom A B n) m f
  · intro ι T f
    exact map_sum (hMapHom A B n) f T

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.hMap_sum_zsmul_add : ∀ (k G : Type) [CommRing k] [Group G] (A B : Rep k G) (n : ℕ), (∀ f g : A ⟶ B, hMap (f + g) n = hMap f n + hMap g n) ∧ hMap (0 : A ⟶ B) n = 0 ∧ (∀ (m : ℤ) (f : A ⟶ B), hMap (m • f) n = m • hMap f n) ∧ ∀ (ι : Type) (T : Finset ι) (f : ι → (A ⟶ B)), hMap (∑ i ∈ T, f i) n = ∑ i ∈ T, hMap (f i) n := by
  first
  | exact @GlobalTheory.HomStab.hMap_additive
  | exact @GlobalTheory.HomStab.hMap_add
  | exact @GlobalTheory.HomStab.chainsMap_id_add
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.StandardSeqPointCompSplitSeqDifferential

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

theorem altSum_neg_one (p : ℕ) : (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ)) = if Even p then 1 else 0 := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    rcases Nat.even_or_odd p with hp | hp
    · have h2 : ¬ Even (p + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hp
      rw [if_pos hp, if_neg h2, pow_succ, hp.neg_one_pow]
      norm_num
    · have h2 : Even (p + 1) := by rw [Nat.even_add_one]; exact Nat.not_even_iff_odd.mpr hp
      rw [if_neg (Nat.not_even_iff_odd.mpr hp), if_pos h2, pow_succ, hp.neg_one_pow]
      norm_num

theorem stab_comp_stab (R : Type) [CommRing R] (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (hac : a ≤ c) :
    (stab R b c hbc).comp (stab R a b hab) = stab R a c hac := by
  ext g i j
  simp only [MonoidHom.comp_apply, stab, Units.coe_map, padHom, MonoidHom.coe_mk, OneHom.coe_mk, padMat, Matrix.of_apply]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;> simp_all [Fin.ext_iff] <;> omega

theorem ptH_comp_hMap_splitD : ∀ (R : Type) [CommRing R] (n p q : ℕ) (h : p + 1 ≤ n) (h₁ : ∀ x, stab R (n - (p + 1)) n (Nat.sub_le _ _) x • stdSeq R n (p + 1) h = stdSeq R n (p + 1) h) (h₀ : ∀ x, stab R (n - p) n (Nat.sub_le _ _) x • stdSeq R n p (by omega) = stdSeq R n p (by omega)), ptH (k := ℤ) (stab R (n - (p + 1)) n (Nat.sub_le _ _)) (stdSeq R n (p + 1) h) h₁ q ≫ hMap (splitD R n p) q = if Even p then grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫ ptH (k := ℤ) (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p (by omega)) h₀ q else 0 := by
  intro R _ n p q h h₁ h₀
  have hσ : (stab R (n - p) n (Nat.sub_le _ _)).comp (stab R (n - (p + 1)) (n - p) (by omega)) =
      stab R (n - (p + 1)) n (Nat.sub_le _ _) := stab_comp_stab R _ _ _ _ _ _
  have hpoint : ∀ (G H H' X Y : Type) [Group G] [Group H] [Group H']
      [MulAction G X] [MulAction G Y] (φ : H →* G) (φ' : H' →* G) (σ : H' →* H)
      (x : X) (hx : ∀ h, φ' h • x = x) (y : Y) (hy : ∀ h, φ h • y = y)
      (f : X → Y) (hf : ∀ (g : G) z, f (g • z) = g • f z) (g : G),
      φ.comp σ = φ' → g • f x = y → (∀ h, g * φ' h = φ' h * g) → ∀ n : ℕ,
      ptH (k := ℤ) φ' x hx n ≫ hMap (permMap f hf (Rep.trivial ℤ G ℤ)) n =
        groupHomology.map (A := Rep.trivial ℤ H' ℤ) (B := Rep.trivial ℤ H ℤ)
          σ (𝟙 (Rep.trivial ℤ H' ℤ)) n ≫ ptH (k := ℤ) φ y hy n := by
    intro G H H' X Y _ _ _ _ _ φ φ' σ x hx y hy f hf g hcomp hgy hc n
    subst hcomp
    have hfx : ∀ h, (φ.comp σ) h • f x = f x := fun h => by rw [← hf, hx]
    have hy' : ∀ h, (φ.comp σ) h • y = y := fun h => hy (σ h)
    have h1 := groupHomology.map_comp (A := Rep.trivial ℤ H' ℤ)
      (B := perm (k := ℤ) (G := G) X) (C := perm (k := ℤ) (G := G) Y)
      (φ.comp σ) (MonoidHom.id G) (ptMap (φ.comp σ) x hx (Rep.trivial ℤ G ℤ))
      (permMap f hf (Rep.trivial ℤ G ℤ)) n
    have hmor : (ptMap (φ.comp σ) x hx (Rep.trivial ℤ G ℤ) ≫
        (Rep.resFunctor (φ.comp σ)).map (permMap f hf (Rep.trivial ℤ G ℤ)) :
          Rep.trivial ℤ H' ℤ ⟶ Rep.res (φ.comp σ) (perm (k := ℤ) (G := G) Y)) =
        ptMap (φ.comp σ) (f x) hfx (Rep.trivial ℤ G ℤ) := by
      ext a
      change (Finsupp.mapDomain f (Finsupp.single x (1 : ℤ))) a = (Finsupp.single (f x) (1 : ℤ)) a
      rw [Finsupp.mapDomain_single]
    have hL : ptH (k := ℤ) (φ.comp σ) x hx n ≫ hMap (permMap f hf (Rep.trivial ℤ G ℤ)) n =
        groupHomology.map (φ.comp σ) (ptMap (φ.comp σ) (f x) hfx (Rep.trivial ℤ G ℤ)) n :=
      h1.symm.trans (congrArg (fun u => groupHomology.map (φ.comp σ) u n) hmor)
    have h2 := groupHomology.map_comp (A := Rep.trivial ℤ H' ℤ) (B := Rep.trivial ℤ H ℤ)
      (C := perm (k := ℤ) (G := G) Y)
      σ φ (𝟙 (Rep.trivial ℤ H' ℤ)) (ptMap φ y hy (Rep.trivial ℤ G ℤ)) n
    have hmor2 : (𝟙 (Rep.trivial ℤ H' ℤ) ≫ (Rep.resFunctor σ).map (ptMap φ y hy (Rep.trivial ℤ G ℤ)) :
          Rep.trivial ℤ H' ℤ ⟶ Rep.res (φ.comp σ) (perm (k := ℤ) (G := G) Y)) =
        ptMap (φ.comp σ) y hy' (Rep.trivial ℤ G ℤ) := by
      ext a
      rfl
    have hR : groupHomology.map (A := Rep.trivial ℤ H' ℤ) (B := Rep.trivial ℤ H ℤ) σ
        (𝟙 (Rep.trivial ℤ H' ℤ)) n ≫ ptH (k := ℤ) φ y hy n =
        groupHomology.map (φ.comp σ) (ptMap (φ.comp σ) y hy' (Rep.trivial ℤ G ℤ)) n :=
      h2.symm.trans (congrArg (fun u => groupHomology.map (φ.comp σ) u n) hmor2)
    rw [hL, hR]
    symm
    refine groupHomology_map_conj ℤ G H' (Rep.trivial ℤ H' ℤ) (perm (k := ℤ) (G := G) Y)
      (φ.comp σ) (φ.comp σ)
      (ptMap (φ.comp σ) (f x) hfx (Rep.trivial ℤ G ℤ)) (ptMap (φ.comp σ) y hy' (Rep.trivial ℤ G ℤ)) g
      (fun h => by rw [hc h, mul_inv_cancel_right]) (fun a => ?_) n
    subst hgy
    change Finsupp.single (g • f x) a =
      Finsupp.mapDomain (fun z => g • z) (Finsupp.mapRange id rfl (Finsupp.single (f x) a))
    rw [Finsupp.mapRange_id, Finsupp.mapDomain_single]
  unfold splitD
  rw [(GlobalTheory.T.hMap_sum_zsmul_add ℤ _ _ _ q).2.2.2 _ Finset.univ, Preadditive.comp_sum]
  rw [Finset.sum_congr rfl (g := fun i : Fin (p + 1) => ((-1 : ℤ) ^ (i : ℕ)) •
      (grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫
        ptH (k := ℤ) (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p (by omega)) h₀ q)) ?_]
  · rw [← Finset.sum_smul, altSum_neg_one]
    split_ifs <;> simp
  · intro i _
    rw [(GlobalTheory.T.hMap_sum_zsmul_add ℤ _ _ _ q).2.2.1, Preadditive.comp_zsmul]
    obtain ⟨g, hg, hc⟩ := GlobalTheory.T.face_stdSeq_GL_conjugate_commuting_stab R n p h i
    have hface := hpoint _ _ _ _ _ (stab R (n - p) n (Nat.sub_le _ _))
      (stab R (n - (p + 1)) n (Nat.sub_le _ _)) (stab R (n - (p + 1)) (n - p) (by omega))
      _ h₁ _ h₀ (face R n p i) (face_smul R n p i) g hσ hg hc q
    exact congrArg (fun m => ((-1 : ℤ) ^ (i : ℕ)) • m) hface

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.standardSeqPoint_comp_splitSeqDifferential : ∀ (R : Type) [CommRing R] (n p q : ℕ) (h : p + 1 ≤ n) (h₁ : ∀ x, stab R (n - (p + 1)) n (Nat.sub_le _ _) x • stdSeq R n (p + 1) h = stdSeq R n (p + 1) h) (h₀ : ∀ x, stab R (n - p) n (Nat.sub_le _ _) x • stdSeq R n p (by omega) = stdSeq R n p (by omega)), ptH (k := ℤ) (stab R (n - (p + 1)) n (Nat.sub_le _ _)) (stdSeq R n (p + 1) h) h₁ q ≫ hMap (splitD R n p) q = if Even p then grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫ ptH (k := ℤ) (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p (by omega)) h₀ q else 0 := by
  first
  | exact @GlobalTheory.HomStab.ptH_comp_hMap_splitD
  | exact @GlobalTheory.HomStab.stab_comp_stab
  | exact @GlobalTheory.HomStab.altSum_neg_one
end
end
end
