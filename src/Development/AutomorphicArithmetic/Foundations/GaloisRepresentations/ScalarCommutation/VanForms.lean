module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQrOneBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicRealisationHolomorphicMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralSimpleAlgebraEmbeddingsConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyAlgHomEqMapMinpoly
public import Mathlib.FieldTheory.Separable
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.OrbZero
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDvdPowOfAevalEqZero

section

@[expose] public section

open Polynomial

namespace GlobalTheory.SepCharpoly

theorem charpoly_dvd_pow_of_aeval_eq_zero {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : R[X]) (hp : aeval M p = 0) : M.charpoly ∣ p ^ Fintype.card n := by
  set a : Matrix n n R[X] := algebraMap R[X] (Matrix n n R[X]) X with ha_def
  set b : Matrix n n R[X] := (Algebra.ofId R R[X]).mapMatrix M with hb_def
  have hab : Commute a b := Algebra.commutes X b
  have key : ∀ q : R[X], ∃ H, (a - b) * H = aeval a q - aeval b q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨H1, h1⟩ := hp
      obtain ⟨H2, h2⟩ := hq
      exact ⟨H1 + H2, by rw [mul_add, h1, h2, map_add (f := _), map_add (f := _)]; abel⟩
    | monomial k c =>
      refine ⟨algebraMap R (Matrix n n R[X]) c * ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i), ?_⟩
      rw [aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc, hab.mul_geom_sum₂,
        mul_sub]
  obtain ⟨H, hH⟩ := key p
  have hb : aeval b p = 0 := by
    rw [hb_def, aeval_algHom_apply, hp, map_zero]
  have ha : aeval a p = algebraMap R[X] (Matrix n n R[X]) p := by
    rw [ha_def, aeval_algebraMap_apply, aeval_X_left_apply]
  have hch : (a - b).det = M.charpoly := rfl
  refine ⟨H.det, ?_⟩
  rw [← hch, ← Matrix.det_mul, hH, hb, sub_zero, ha, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal]
  simp

theorem not_separable_charpoly : ∀ (F L C : Type) [Field F] [Field L] [Algebra F L] [Ring C] [Algebra F C]
    [FiniteDimensional F C] (n : ℕ) (ι : C →ₐ[F] Matrix (Fin n) (Fin n) L) (y : C),
    ((minpoly F y).natDegree < n ∨ ((minpoly F y).natDegree = n ∧ ¬ (minpoly F y).Separable)) →
      ¬ (ι y).charpoly.Separable := by
  intro F L C _ _ _ _ _ _ n ι y h hc
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hpm : (minpoly F y).Monic := minpoly.monic hyi
  have h1 : aeval (ι y) ((minpoly F y).map (algebraMap F L)) = 0 := by
    rw [aeval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
  have h2 : minpoly L (ι y) ∣ (minpoly F y).map (algebraMap F L) := minpoly.dvd L _ h1
  have h3 : (ι y).charpoly ∣ (minpoly L (ι y)) ^ Fintype.card (Fin n) :=
    charpoly_dvd_pow_of_aeval_eq_zero _ _ (minpoly.aeval L _)
  have h4 : (ι y).charpoly ∣ minpoly L (ι y) := hc.squarefree.isRadical _ _ h3
  have h5 := h4.trans h2
  have hmm : ((minpoly F y).map (algebraMap F L)).Monic := hpm.map _
  have hdc : (ι y).charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hdm : ((minpoly F y).map (algebraMap F L)).natDegree = (minpoly F y).natDegree := natDegree_map _
  rcases h with h | ⟨h, hns⟩
  · have := natDegree_le_of_dvd h5 hmm.ne_zero
    omega
  · have e := eq_of_monic_of_dvd_of_natDegree_le (Matrix.charpoly_monic _) hmm h5 (by omega)
    rw [← e] at hc
    exact hns ((separable_map (algebraMap F L)).mp hc)

end GlobalTheory.SepCharpoly
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbKEqZeroOfCharpolyNotSeparable

section

@[expose] public section

namespace GlobalTheory

theorem orbK_eq_zero_of_charpoly_not_separable (G : Type) [Group G] (k : Type) [Field k] (n : ℕ)
    (π : G →* GL (Fin n) k) (K : Subgroup G) (δ : G) (f : G → ℂ)
    (hf : ∀ g, f g ≠ 0 → ((π g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly.Separable)
    (hδ : ¬ ((π δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly.Separable) :
    GlobalTheory.LKCount.orbK (MonoidHom.id G) K δ f = 0 := by
  unfold GlobalTheory.LKCount.orbK GlobalTheory.LKCount.orbC
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  have hz : ∀ x : G, f (x⁻¹ * δ * x) = 0 := by
    intro x
    by_contra h
    apply hδ
    have hs := hf _ h
    have hc : ((π (x⁻¹ * δ * x) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly
        = ((π δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly := by
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
        Matrix.charpoly_mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rwa [hc] at hs
  simp [hz]

end GlobalTheory
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.VanForms

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.LKCount
  GlobalTheory.LKCount.OrbKProd GlobalTheory.BCT UpperTheory.Gal.LocalSmoothExtension
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

variable {p : ℕ} [Fact p.Prime]

private def atHom {G : HTGroup p} {k : Type} [Field k] [Algebra G.F k] (P : Pl G k) : G.GAf →* GL (Fin G.n) k :=
  (Units.map (P.κ : AfP p ⊗[ℚ] G.C →* Matrix (Fin G.n) (Fin G.n) k)).comp
    ((MonoidHom.fst _ _).comp (Subgroup.subtype _))

private theorem charpoly_at_toAfF {G : HTGroup p} {k : Type} [Field k] [Algebra G.F k] (P : Pl G k) (β : G.Cˣ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : grp G β) :
    (P.at (toAfF G β x t hx y)).charpoly = (P.ι ((y.1.1 : G.Cˣ) : G.C)).charpoly := by
  have h := Matrix.charpoly_units_conj (Units.map (P.κ : AfP p ⊗[ℚ] G.C →* Matrix (Fin G.n) (Fin G.n) k) x)
    (P.ι ((y.1.1 : G.Cˣ) : G.C))
  rw [← h, ← P.κ_ι]
  have e : P.at (toAfF G β x t hx y) =
      P.κ (x : AfP p ⊗[ℚ] G.C) * P.κ (1 ⊗ₜ ((y.1.1 : G.Cˣ) : G.C)) * P.κ ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by
    rw [← map_mul, ← map_mul]
    rfl
  rw [e, ← Matrix.coe_units_inv]
  rfl

private theorem toAfF_cent_comm {G : HTGroup p} (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (hdeg : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable) :
    ∀ a ∈ twCent (MonoidHom.id G.GAf) (toAfF G β x t hx y),
    ∀ b ∈ twCent (MonoidHom.id G.GAf) (toAfF G β x t hx y), a * b = b * a := by
  have hcsa := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC ((y.1.1 : G.Cˣ) : G.C) hsep hdeg
  have hcent : ∀ w : G.C, w * ((y.1.1 : G.Cˣ) : G.C) = ((y.1.1 : G.Cˣ) : G.C) * w ↔
      w ∈ Set.range ((Algebra.adjoin G.F ({((y.1.1 : G.Cˣ) : G.C)} : Set G.C)).val.restrictScalars ℚ) := by
    intro w
    constructor
    · intro h
      have hw : w ∈ Subalgebra.centralizer G.F {((y.1.1 : G.Cˣ) : G.C)} := by
        rw [Subalgebra.mem_centralizer_iff]
        simpa using h.symm
      rw [hcsa] at hw
      exact ⟨⟨w, hw⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      have hw : (v : G.C) ∈ Subalgebra.centralizer G.F {((y.1.1 : G.Cˣ) : G.C)} := by rw [hcsa]; exact v.2
      rw [Subalgebra.mem_centralizer_iff] at hw
      exact (hw _ rfl).symm
  set U : (AfP p ⊗[ℚ] G.C)ˣ := Units.map (inC G (AfP p)).toMonoidHom y.1.1 with hU
  have hUv : (U : AfP p ⊗[ℚ] G.C) = (1 : AfP p) ⊗ₜ[ℚ] ((y.1.1 : G.Cˣ) : G.C) := rfl
  have hδ : ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 = x * U * x⁻¹ := rfl
  have conj : ∀ a ∈ twCent (MonoidHom.id G.GAf) (toAfF G β x t hx y),
      (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) *
          ((1 : AfP p) ⊗ₜ[ℚ] ((y.1.1 : G.Cˣ) : G.C)) =
        ((1 : AfP p) ⊗ₜ[ℚ] ((y.1.1 : G.Cˣ) : G.C)) *
          (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) := by
    intro a ha
    have h1 := congrArg (fun g : G.GAf => (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1) ha
    simp only [Subgroup.coe_mul, Prod.fst_mul, MonoidHom.id_apply] at h1
    rw [hδ] at h1
    set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
    have h2 : x⁻¹ * A * x * U = U * (x⁻¹ * A * x) := by
      calc x⁻¹ * A * x * U = x⁻¹ * (A * (x * U * x⁻¹)) * x := by group
        _ = x⁻¹ * (x * U * x⁻¹ * A) * x := by rw [h1]
        _ = U * (x⁻¹ * A * x) := by group
    rw [← hUv, ← Units.val_mul, ← Units.val_mul, h2]
  intro a ha b hb
  have hc := GlobalTheory.LKCentAf.commute_of_centralizer ℚ (AfP p) G.C _ ((y.1.1 : G.Cˣ) : G.C) _ hcent _ _ (conj a ha) (conj b hb)
  set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  set B := (b : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  have hc' : (x⁻¹ * A * x) * (x⁻¹ * B * x) = (x⁻¹ * B * x) * (x⁻¹ * A * x) := Units.ext (by
    simpa only [Units.val_mul] using hc)
  have hAB : A * B = B * A := by
    calc A * B = x * ((x⁻¹ * A * x) * (x⁻¹ * B * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * B * x) * (x⁻¹ * A * x)) * x⁻¹ := by rw [hc']
      _ = B * A := by group
  apply Subtype.ext
  apply Prod.ext
  · simpa only [Subgroup.coe_mul, Prod.fst_mul] using hAB
  · simp only [Subgroup.coe_mul, Prod.snd_mul]
    exact mul_comm _ _

private theorem twisted_centralizer_commutative {G : HTGroup p} (β : G.Cˣ) (y : grp G β)
    (hdeg : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n)
    (hsep : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable) :
    ∀ a ∈ twCent (MonoidHom.id (Gr G 1)) (toP1 G β y),
    ∀ b ∈ twCent (MonoidHom.id (Gr G 1)) (toP1 G β y), a * b = b * a := by
  have hrho : ∀ w, (G.rho w ((y.1.1 : G.Cˣ) : G.C)).charpoly.Separable := by
    intro w
    letI : Algebra G.F (G.Fw w) := (G.embW w).toAlgebra
    have hg : ∀ a, G.rho w (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) a :=
      fun a => by rw [G.rho_F, Matrix.algebraMap_eq_diagonal]; rfl
    let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) (G.Fw w) := { G.rho w with commutes' := hg }
    have h := GlobalTheory.charpoly_algHom_eq_map_minpoly G.F (G.Fw w) G.C G.n G.rankC g _ hdeg
    have e : g ((y.1.1 : G.Cˣ) : G.C) = G.rho w ((y.1.1 : G.Cˣ) : G.C) := rfl
    rw [e] at h
    rw [h]
    exact hsep.map
  have hb := GlobalTheory.TorCls.AtP.inclG_one_bijective G
  have hy : toP1 G β y = inclG G 1 (locC G y.1) := rfl
  have key : ∀ a ∈ twCent (MonoidHom.id (Gr G 1)) (toP1 G β y), ∃ a' : Gp G, inclG G 1 a' = a ∧
      a' * locC G y.1 = locC G y.1 * a' := by
    intro a ha
    obtain ⟨a', rfl⟩ := hb.2 a
    refine ⟨a', rfl, hb.1 ?_⟩
    rw [map_mul, map_mul, ← hy]
    exact ha
  intro a ha b hb'
  obtain ⟨a', rfl, ha'⟩ := key a ha
  obtain ⟨b', rfl, hb''⟩ := key b hb'
  rw [← map_mul, ← map_mul]
  congr 1
  refine Prod.ext (mul_comm _ _) (funext fun w => ?_)
  exact GlobalTheory.CentSep.centraliser_comm_of_separable (G.Fw w) (Fin G.n) ((locC G y.1).2 w) (a'.2 w) (b'.2 w) (hrho w)
    (congrFun (congrArg Prod.snd ha') w) (congrFun (congrArg Prod.snd hb'') w)

end UpperTheory.Gal.Spc

open UpperTheory.Gal.Spc in
theorem UpperTheory.Gal.Spc.vanForms :
    UpperTheory.Gal.Spc.VanForms := by
  intro p _ G _ Lv k _ _ _ _ _ _ _ P H _ _ _ _ S k₁ _ _ P₁ f hf hC hR B x t hx y hy
  by_cases hs1 : (P₁.ι ((y.1.1 : G.Cˣ) : G.C)).charpoly.Separable
  · have hns := GlobalTheory.SepCharpoly.not_separable_charpoly G.F k₁ G.C G.n P₁.ι ((y.1.1 : G.Cˣ) : G.C)
    have hle := GlobalTheory.VanishNonEll.natDegree_minpoly_le G.F k₁ G.C G.n G.n_pos P₁.ι ((y.1.1 : G.Cˣ) : G.C)
    have hdeg : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n := by
      by_contra h
      exact hns (Or.inl (lt_of_le_of_ne hle h)) hs1
    have hms : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable := by
      by_contra h
      exact hns (Or.inr ⟨hdeg, h⟩) hs1
    have hirr : ¬ Irreducible (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)) := fun h => hy ⟨hdeg, hms, h⟩
    have hcp := GlobalTheory.charpoly_algHom_eq_map_minpoly G.F k G.C G.n G.rankC P.ι ((y.1.1 : G.Cˣ) : G.C) hdeg
    have hat := charpoly_at_toAfF P B.β x t hx y
    rw [hcp] at hat
    have hδs : (P.at (toAfF G B.β x t hx y)).charpoly.Separable := by
      rw [hat]
      exact hms.map
    have hδi : ¬ Irreducible (P.at (toAfF G B.β x t hx y)).charpoly := by
      rw [hat]
      exact GlobalTheory.VanishNonEll.not_irreducible_map _ _ (minpoly.monic (IsIntegral.of_finite G.F _)) hirr
    have hT₁ := toAfF_cent_comm B.β x t hx y hdeg hms
    have hT₂ := twisted_centralizer_commutative B.β y hdeg hms
    have h1 := orbK_eq_zero_of_cuspSlices S f hf hC _ hδs hδi hT₁
    have hbi : Formalism.UG.IsBiInv Lv.K.toSubgroup f := hf.1
    refine orbK_prod_eq_zero_of_slices Lv.K.toSubgroup (Kp G) (toAfF G B.β x t hx y) (toP1 G B.β y) _ hT₁ hT₂ ?_ fun z => ?_
    · intro c hc w
      rw [Subgroup.mem_prod] at hc
      have e1 : f (c.1⁻¹ * w.1 * c.1) = f w.1 :=
        hbi ⟨c.1⁻¹, Subgroup.inv_mem _ hc.1⟩ ⟨c.1, hc.1⟩ _
      have e2 : oneP G (c.2⁻¹ * w.2 * c.2) = oneP G w.2 := by
        have hiff : c.2⁻¹ * w.2 * c.2 ∈ Kp G ↔ w.2 ∈ Kp G := by
          rw [(Kp G).mul_mem_cancel_right hc.2, (Kp G).mul_mem_cancel_left ((Kp G).inv_mem hc.2)]
        unfold oneP
        by_cases hw : w.2 ∈ Kp G
        · rw [Set.indicator_of_mem (show _ ∈ (Kp G : Set (Gr G 1)) from hiff.2 hw),
            Set.indicator_of_mem (show _ ∈ (Kp G : Set (Gr G 1)) from hw)]
          rfl
        · rw [Set.indicator_of_notMem (show _ ∉ (Kp G : Set (Gr G 1)) from fun h => hw (hiff.1 h)),
            Set.indicator_of_notMem (show _ ∉ (Kp G : Set (Gr G 1)) from hw)]
      show f (c.1⁻¹ * w.1 * c.1) * oneP G (c.2⁻¹ * w.2 * c.2) = f w.1 * oneP G w.2
      rw [e1, e2]
    · unfold orbK at h1 ⊢
      rw [orbC_eq] at h1 ⊢
      have e : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id G.GAf) (toAfF G B.β x t hx y) : Set G.GAf)
          (Lv.K.toSubgroup : Set G.GAf),
          oTerm (MonoidHom.id G.GAf) Lv.K.toSubgroup
            (twCent (MonoidHom.id G.GAf) (toAfF G B.β x t hx y) ⊓ Lv.K.toSubgroup) (toAfF G B.β x t hx y)
            (fun v => f v * oneP G z) (Quotient.out q) =
          oneP G z * oTerm (MonoidHom.id G.GAf) Lv.K.toSubgroup
            (twCent (MonoidHom.id G.GAf) (toAfF G B.β x t hx y) ⊓ Lv.K.toSubgroup) (toAfF G B.β x t hx y) f
            (Quotient.out q) := by
        intro q
        unfold oTerm
        ring
      rw [finsum_congr e]
      exact finsum_mul_eq_zero _ _ h1
  · refine GlobalTheory.orbK_eq_zero_of_charpoly_not_separable _ k₁ G.n ((atHom P₁).comp (MonoidHom.fst _ _)) _ _ _ ?_ ?_
    · intro g hg
      exact hR g.1 (left_ne_zero_of_mul hg)
    · intro h
      apply hs1
      rw [← charpoly_at_toAfF P₁ B.β x t hx y]
      exact h
end
end
end
