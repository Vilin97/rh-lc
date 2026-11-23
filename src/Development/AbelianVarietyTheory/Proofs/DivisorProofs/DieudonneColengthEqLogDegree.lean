module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueKernelOrderPPowerDegreeIsogenyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasKernelOrderPPowerDegreeCompLeAddStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenousPDivGroupFinrankOmegaDualStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentKernelEqCokerOmegaMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientKernelSupFrobeniusKernelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientPDivGroupClosedSubgroupPTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIsogenyOmegaAndDualSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthRangeMapGeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusKernelHopfLePowCotangent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKernelIdealEqBeyondExponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenousPDivGroupFinrankOmegaDual
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsogenyHeightEqDualSameDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupExistsFactorThroughIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupIsogenyBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthCompositionStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthOfHeightOne

section

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.ColengthHtOne

open Module

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem le_finrank_coker_omegaMap [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ)
    (h1 : q ≫ q' = (p : ℤ_[p]) • 𝟙 G) (hF : frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1))
    (he : HasLogDeg q e) : e ≤ finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) := by
  unfold HasLogDeg at he
  obtain ⟨N, hN⟩ := he
  have hlev : finrank k (G.A 1 ⧸ kerIdeal (q.app 1)) = p ^ e := by
    rw [← GlobalTheory.Dieu.finrank_quot_kerIdeal_eq p k G H 1 (max N 1) q q' (by rw [pow_one]; exact h1)
      (le_max_right _ _)]
    exact hN _ (le_max_left _ _)
  obtain ⟨C, _, _, _, _, π, hπ, hker, hnil, hFaug⟩ := GlobalTheory.T.exists_quotient_kernel_sup_frobeniusKernel p k G H q
  have hker' : RingHom.ker π = kerIdeal (q.app 1) := by rw [hker]; exact sup_eq_left.2 hF
  have hC : finrank k C = p ^ e := by
    rw [← hlev, ← hker']
    exact ((Ideal.quotientKerAlgEquivOfSurjective (f := (π : G.A 1 →ₐ[k] C)) hπ).toLinearEquiv.finrank_eq).symm
  have hfrobC : frobKerIdeal p k C = ⊥ := by
    rw [eq_bot_iff]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    simp [hnil a ha]
  have hCq : finrank k C = finrank k (C ⧸ frobKerIdeal p k C) := by
    refine LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Ideal.Quotient.mkₐ k (frobKerIdeal p k C)).toLinearMap
      ⟨fun a b h => ?_, Ideal.Quotient.mkₐ_surjective k _⟩)
    have h' := Ideal.Quotient.eq.1 h
    rwa [hfrobC, Ideal.mem_bot, sub_eq_zero] at h'
  have hle := GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot p k C
  rw [← hCq, hC] at hle
  have hcot := (GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k G H q C π hπ).2.1 (by rw [hker]; exact sup_le_sup_left hFaug _) hker'.ge
  rw [hcot]
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle

theorem finrank_coker_lieMap {A B : PDivGroup p k} (f : A ⟶ B) [FiniteDimensional k A.omega]
    [FiniteDimensional k B.omega] (hd : finrank k A.omega = finrank k B.omega) :
    finrank k (B.Lie ⧸ LinearMap.range (lieMap A B f)) =
      finrank k (A.omega ⧸ LinearMap.range (omegaMap A B f)) := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range (lieMap A B f))
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range (omegaMap A B f))
  have h3 : finrank k (LinearMap.range (lieMap A B f)) = finrank k (LinearMap.range (omegaMap A B f)) :=
    LinearMap.finrank_range_dualMap_eq_finrank_range (omegaMap A B f)
  have h4 : finrank k B.Lie = finrank k B.omega := Subspace.dual_finrank_eq
  omega

theorem finrank_coker_lieMap_congr {A B A' B' : PDivGroup p k} (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B)
    (f' : A' ⟶ B') (hc : eA.hom ≫ f' = f ≫ eB.hom) :
    finrank k (B'.Lie ⧸ LinearMap.range (lieMap A' B' f')) =
      finrank k (B.Lie ⧸ LinearMap.range (lieMap A B f)) := by
  let L : B.Lie ≃ₗ[k] B'.Lie := LinearEquiv.ofLinear (lieMap B B' eB.hom) (lieMap B' B eB.inv)
    (by rw [← lieMap_comp, eB.inv_hom_id, lieMap_id]) (by rw [← lieMap_comp, eB.hom_inv_id, lieMap_id])
  have hA : LinearMap.range (lieMap A A' eA.hom) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun x => ⟨lieMap A' A eA.inv x, ?_⟩
    rw [← LinearMap.comp_apply, ← lieMap_comp, eA.inv_hom_id, lieMap_id, LinearMap.id_apply]
  have hr : LinearMap.range (lieMap A' B' f') = (LinearMap.range (lieMap A B f)).map (L : B.Lie →ₗ[k] B'.Lie) := by
    rw [← LinearMap.range_comp_of_range_eq_top _ hA, ← lieMap_comp, hc, lieMap_comp, LinearMap.range_comp]
    rfl
  rw [hr]
  exact (Submodule.Quotient.equiv _ _ L rfl).finrank_eq.symm

end GlobalTheory.Dieu.ColengthHtOne


open GlobalTheory.Dieu.ColengthHtOne in
theorem GlobalTheory.Dieu.le_colength_of_htOne : ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ), q ≫ q' = (p : ℤ_[p]) • 𝟙 G →
    q' ≫ q = (p : ℤ_[p]) • 𝟙 H → frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1) → HasLogDeg q e →
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M H.dual ⧸ LinearMap.range (T.map (dualHom G H q))) ∧
    e ≤ Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) := by
  intro p _ T k _ _ _ G H q q' e h1 h2 hF he
  have h3 := le_finrank_coker_omegaMap G H q q' e h1 hF he
  have hp0 : (p : k) = 0 := CharP.cast_eq_zero k p
  haveI := GlobalTheory.PDivGroup.finite_omega_of_eq_zero hp0 G
  haveI := GlobalTheory.PDivGroup.finite_omega_of_eq_zero hp0 H
  have hiso : IsIsog q := by
    unfold IsIsog
    exact ⟨1, q', by simpa only [pow_one] using h1, by simpa only [pow_one] using h2⟩
  have hd := (GlobalTheory.Dieu.isog_finrank_omega p T k G H q hiso).2.2.1
  have hL := (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k H.dual G.dual (dualHom G H q)).2
  rw [finrank_coker_lieMap_congr G.bidual H.bidual q _ (bidual_hom_dualHom_dualHom q),
    finrank_coker_lieMap q hd] at hL
  refine ⟨le_trans (by exact_mod_cast h3) (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k G H q).1, le_trans (by exact_mod_cast h3) hL, h3⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthOfHeightOneStatement

section

@[expose] public section

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne
    (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ)
    (h₁ : q ≫ q' = (p : ℤ_[p]) • 𝟙 G) (h₂ : q' ≫ q = (p : ℤ_[p]) • 𝟙 H)
    (hF : frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1)) (he : GlobalTheory.Dieu.HasLogDeg q e) :
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
      (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M H.dual ⧸ LinearMap.range (T.map (dualHom G H q))) ∧
      e ≤ Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) :=
  GlobalTheory.Dieu.le_colength_of_htOne p T k G H q q' e h₁ h₂ hF he
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColength

section

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.ColengthDegree

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_comp {X Y Z : PDivGroup p k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    T.map (f ≫ g) = T.map f ∘ₗ T.map g :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k X Y Z trivial trivial trivial).2.1 f g

theorem map_id (X : PDivGroup p k) : T.map (𝟙 X) = LinearMap.id :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k X X X trivial trivial trivial).1

theorem map_iso_bijective {X Y : PDivGroup p k} (i : X ≅ Y) : Function.Bijective (T.map i.hom) := by
  have e₁ : T.map i.inv ∘ₗ T.map i.hom = LinearMap.id := by rw [← map_comp, i.inv_hom_id, map_id]
  constructor
  · exact Function.LeftInverse.injective (g := T.map i.inv) fun a => congrArg (fun g => g a) e₁
  · intro a
    refine ⟨T.map i.inv a, ?_⟩
    have e : T.map i.hom ∘ₗ T.map i.inv = LinearMap.id := by rw [← map_comp, i.hom_inv_id, map_id]
    exact congrArg (fun g => g a) e

theorem colen_comp {X Y Z : PDivGroup p k} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : Function.Injective (T.map f)) :
    Module.length (WittVector p k) (T.M X ⧸ LinearMap.range (T.map (f ≫ g))) =
      Module.length (WittVector p k) (T.M X ⧸ LinearMap.range (T.map f)) +
        Module.length (WittVector p k) (T.M Y ⧸ LinearMap.range (T.map g)) := by
  rw [map_comp]
  exact (GlobalTheory.T.witt_module_length_composition p k (T.M X) (T.M Y) (T.M Z)).1 _ _ hf

theorem colen_iso {X Y : PDivGroup p k} (i : X ≅ Y) :
    Module.length (WittVector p k) (T.M X ⧸ LinearMap.range (T.map i.hom)) = 0 := by
  rw [LinearMap.range_eq_top.2 (map_iso_bijective T i).2]
  exact Module.length_eq_zero_iff.2 inferInstance


omit [PerfectRing k p] in
theorem omegaMap_surjective_of_isIso {X Y : PDivGroup p k} (f : X ⟶ Y) [IsIso f] :
    Function.Surjective (omegaMap X Y f) := by
  intro w
  refine ⟨omegaMap Y X (inv f) w, ?_⟩
  rw [← LinearMap.comp_apply, ← omegaMap_comp, IsIso.hom_inv_id, omegaMap_id, LinearMap.id_apply]


omit [PerfectRing k p] in
theorem exists_step {X Y : PDivGroup p k} (f : X ⟶ Y) (hω : ¬ Function.Surjective (omegaMap X Y f)) :
    ∃ (Q : PDivGroup p k) (q₁ : X ⟶ Q) (q₁' : Q ⟶ X) (r : Q ⟶ Y),
      q₁ ≫ q₁' = (p : ℤ_[p]) • 𝟙 X ∧ q₁' ≫ q₁ = (p : ℤ_[p]) • 𝟙 Q ∧
      frobKerIdeal p k (X.A 1) ≤ kerIdeal (q₁.app 1) ∧ q₁ ≫ r = f ∧
      ¬ Function.Surjective (omegaMap X Q q₁) := by
  obtain ⟨C, _, _, _, _, π, hπs, hker, -, hfrob⟩ := GlobalTheory.T.exists_quotient_kernel_sup_frobeniusKernel p k X Y f
  obtain ⟨Q, q₁, q₁', h1, h2, hk1⟩ := GlobalTheory.T.exists_quotient_pDivGroup_closedSubgroup_pTorsion p k X C π hπs
  have hle : kerIdeal (f.app 1) ≤ kerIdeal (q₁.app 1) := by rw [hk1, hker]; exact le_sup_left
  obtain ⟨r, hr⟩ := GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k X Q Y 1 q₁ q₁' f (by rw [pow_one]; exact h1)
    (by rw [pow_one]; exact h2) hle
  refine ⟨Q, q₁, q₁', r, h1, h2, by rw [hk1, hker]; exact le_sup_right, hr, ?_⟩
  intro hs
  apply hω
  have e1 := (GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k X Q q₁ C π hπs).2.1 (by rw [hk1]; exact le_sup_left) (by rw [hk1])
  have e2 := (GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k X Y f C π hπs).2.1 (by rw [hker]; exact sup_le_sup_left hfrob _)
    (by rw [hker]; exact le_sup_left)
  haveI := finite_omega_of_eq_zero (CharP.cast_eq_zero k p) X
  have h0 : Module.finrank k (X.omega ⧸ LinearMap.range (omegaMap X Q q₁)) = 0 := by
    rw [LinearMap.range_eq_top.2 hs]
    exact Module.finrank_zero_of_subsingleton
  rw [e1, ← e2] at h0
  have hsub := Module.finrank_zero_iff.1 h0
  rw [← LinearMap.range_eq_top, eq_top_iff]
  intro x _
  exact (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)


omit [PerfectRing k p] in
theorem one_le_deg {X Q : PDivGroup p k} (q₁ : X ⟶ Q) (q₁' : Q ⟶ X)
    (h1 : q₁ ≫ q₁' = (p : ℤ_[p]) • 𝟙 X) (h2 : q₁' ≫ q₁ = (p : ℤ_[p]) • 𝟙 Q)
    (hns : ¬ Function.Surjective (omegaMap X Q q₁)) (e₁ : ℕ) (he₁ : HasLogDeg q₁ e₁) : 1 ≤ e₁ := by
  rcases Nat.eq_zero_or_pos e₁ with h | h
  · subst h
    have hI : IsIsog q₁ := ⟨1, q₁', by rw [pow_one]; exact h1, by rw [pow_one]; exact h2⟩
    haveI := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k X).2.2.2 Q q₁ hI).1 he₁
    exact absurd (omegaMap_surjective_of_isIso q₁) hns
  · exact h

theorem kernelDegree_le_dieudonneColength_of_colength_eq (n : ℕ) : ∀ (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = n → e ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G H q e hq he hn
  by_cases hA : Function.Surjective (omegaMap G H q)
  · by_cases hB : Function.Surjective (omegaMap H.dual G.dual (dualHom G H q))
    · haveI := GlobalTheory.T.isIso_isogeny_omega_and_dual_surjective p k G H q hq hA hB
      have h0 : HasLogDeg q 0 := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).2.2.2 H q hq).2 inferInstance
      have := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k G H q hq).unique he h0
      omega
    · obtain ⟨Q, q₁, q₁', r, h1, h2, hfr, hr, hns⟩ := exists_step (dualHom G H q) hB
      have hg := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k G H q hq
      have hq₁ : IsIsog q₁ := ⟨1, q₁', by rw [pow_one]; exact h1, by rw [pow_one]; exact h2⟩
      have hrI : IsIsog r := (GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k H.dual).2.2.1 Q G.dual q₁ r hq₁ (hr ▸ hg.2.1)
      obtain ⟨e₁, he₁⟩ := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k H.dual Q q₁ hq₁).exists
      obtain ⟨e₂, he₂⟩ := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k Q G.dual r hrI).exists
      have hle : e ≤ e₁ + e₂ :=
        GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add p k H.dual Q G.dual q₁ r e₁ e₂ e he₁ he₂ (hr ▸ hg.2.2 e he)
      have h1e := one_le_deg q₁ q₁' h1 h2 hns e₁ he₁
      have hL1 := (GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne p T k H.dual Q q₁ q₁' e₁ h1 h2 hfr he₁).2.1
      have hgr := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k Q G.dual r hrI
      have hg₁ := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k H.dual Q q₁ hq₁
      have hcomp : dualHom _ _ (dualHom G H q) = dualHom Q G.dual r ≫ dualHom H.dual Q q₁ := by
        rw [← hr]; rfl
      have hlen : Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) =
          Module.length (WittVector p k)
              (T.M G.dual.dual ⧸ LinearMap.range (T.map (dualHom Q G.dual r))) +
            Module.length (WittVector p k)
              (T.M Q.dual ⧸ LinearMap.range (T.map (dualHom H.dual Q q₁))) := by
        have a1 := colen_comp T G.bidual.hom (dualHom _ _ (dualHom G H q)) (map_iso_bijective T _).1
        have a2 := colen_comp T q H.bidual.hom (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hq).1
        rw [bidual_hom_dualHom_dualHom q, a2] at a1
        simp only [colen_iso, add_zero, zero_add] at a1
        rw [a1, hcomp, colen_comp T _ _ (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k _ _ _ hgr.2.1).1]
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k _ _ _ hgr.2.1).2.1
      obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k _ _ _ hg₁.2.1).2.1
      rw [← ha, ← hb] at hlen
      rw [← hb] at hL1
      rw [hlen] at hn
      have hab : a + b = n := by exact_mod_cast hn
      have hbe : e₁ ≤ b := by exact_mod_cast hL1
      have := ih a (by omega) _ _ (dualHom Q G.dual r) e₂ hgr.2.1 (hgr.2.2 e₂ he₂) ha.symm
      omega
  · obtain ⟨Q, q₁, q₁', r, h1, h2, hfr, hr, hns⟩ := exists_step q hA
    have hq₁ : IsIsog q₁ := ⟨1, q₁', by rw [pow_one]; exact h1, by rw [pow_one]; exact h2⟩
    have hrI : IsIsog r := (GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).2.2.1 Q H q₁ r hq₁ (hr ▸ hq)
    obtain ⟨e₁, he₁⟩ := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k G Q q₁ hq₁).exists
    obtain ⟨e₂, he₂⟩ := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k Q H r hrI).exists
    have hle : e ≤ e₁ + e₂ := GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add p k G Q H q₁ r e₁ e₂ e he₁ he₂ (hr ▸ he)
    have h1e := one_le_deg q₁ q₁' h1 h2 hns e₁ he₁
    have hL1 := (GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne p T k G Q q₁ q₁' e₁ h1 h2 hfr he₁).1
    have hlen := colen_comp T q₁ r (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G Q q₁ hq₁).1
    rw [hr] at hlen
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G Q q₁ hq₁).2.1
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k Q H r hrI).2.1
    rw [← ha, ← hb] at hlen
    rw [← ha] at hL1
    rw [hlen] at hn
    have hab : a + b = n := by exact_mod_cast hn
    have hae : e₁ ≤ a := by exact_mod_cast hL1
    have := ih b (by omega) _ _ r e₂ hrI he₂ hb.symm
    omega

end GlobalTheory.Dieu.ColengthDegree

namespace GlobalTheory.Dieu

theorem le_length_coker_of_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) := by
  intro p _ T k _ _ _ G H q e hq he
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hq).2.1
  rw [← hn]
  exact_mod_cast ColengthDegree.kernelDegree_le_dieudonneColength_of_colength_eq T n G H q e hq he hn.symm

end GlobalTheory.Dieu
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthStatement

section

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.kernelDegree_le_dieudonneColength : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e → (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) := by
  first | exact @GlobalTheory.Dieu.le_length_coker_of_hasLogDeg | exact GlobalTheory.Dieu.le_length_coker_of_hasLogDeg | (intros; apply GlobalTheory.Dieu.le_length_coker_of_hasLogDeg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneColengthEqLogDegree

section

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem length_quot_range_map_eq_of_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = e := by
  intro p _ T k _ _ _ G H q e hq he
  obtain ⟨n, g, hqg, hgq⟩ := hq
  have hq' : IsIsog q := ⟨n, g, hqg, hgq⟩
  have hg : IsIsog g := ⟨n, q, hgq, hqg⟩
  obtain ⟨e', he', -⟩ := GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k H G g hg
  have hpG := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).1 n).2
  rw [← hqg] at hpG
  have hle : n * G.height ≤ e + e' := GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add p k G H G q g e e' _ he he' hpG
  have h1 := GlobalTheory.T.kernelDegree_le_dieudonneColength p T k G H q e hq' he
  have h2 := GlobalTheory.T.kernelDegree_le_dieudonneColength p T k H G g e' hg he'
  obtain ⟨hinj, hfin1, -⟩ := GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hq'
  obtain ⟨-, hfin2, -⟩ := GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k H G g hg
  obtain ⟨hid, hcomp, -, -, -, -, -, hrank, -⟩ :=
    GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H G trivial trivial trivial
  obtain ⟨-, -, -, -, hsmulG, -⟩ :=
    GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  obtain ⟨hadd, hpow, -⟩ := GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) (T.M G)
  have hsum := hadd (T.map q) (T.map g) hinj
  have hcomp' : T.map q ∘ₗ T.map g = T.map (q ≫ g) := (hcomp q g).symm
  have hmul : ∀ a : T.M G, (T.map q ∘ₗ T.map g) a = p ^ n • a := by
    intro a
    rw [hcomp', hqg]
    show T.base.map trivial trivial ((p : ℤ_[p]) ^ n • 𝟙 G) a = p ^ n • a
    rw [hsmulG n (𝟙 G) a, hid]
    rfl
  have hn := hpow (T.base.free G trivial) (T.base.finite G trivial) n _ hmul
  rw [hn, hrank] at hsum
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfin1
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hfin2
  rw [← ha] at h1 hsum ⊢
  rw [← hb] at h2 hsum
  norm_cast at h1 h2 hsum ⊢
  omega

end GlobalTheory.Dieu
end
end
