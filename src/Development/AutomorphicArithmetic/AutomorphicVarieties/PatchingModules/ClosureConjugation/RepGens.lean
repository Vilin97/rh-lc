module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TriProdZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.EpsEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.StarBasic
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.RepStar

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.rep_star :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ y, P.rep (G.frame.star O B n y) = (P.rep y)ᵀ := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P y
  have sb := star_basic G.frame n O B
  have hrep : ∀ (g : G.G₀) (b : B), P.rep (MonoidAlgebra.single g b) = P.f b • mat x.ρ (h.p₀ g) := by
    intro g b
    simp only [OoPt.rep, GDet.repAlg, RingHom.comp_apply, MonoidAlgebra.mapRingHom_single,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.comp_apply,
      Algebra.algebraMap_self, RingHom.mapMatrix_id]
    rfl
  induction y using MonoidAlgebra.induction_linear with
  | zero =>
    have h0 : G.frame.star O B n 0 = 0 := by simpa using sb.2.2.2.2.2.1 0 0
    rw [h0, map_zero, Matrix.transpose_zero]
  | add p q hp hq => rw [sb.2.2.1, map_add (f := _), map_add (f := _), hp, hq, Matrix.transpose_add]
  | single g b =>
    rw [sb.2.2.2.2.2.2 g b]
    obtain ⟨he, hc⟩ := eps_eq P g
    have hform := x.form (h.p₀ g)
    rw [Units.val_one, mul_one] at hform
    have hci : mat x.ρ (G0.frame.conj (h.p₀ g)) * mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hT : (mat x.ρ (h.p₀ g))ᵀ =
        ((G0.frame.eps ℤ_[l] (PowerSeries x.K) (h.p₀ g) ^ (1 - (n : ℤ)) : (PowerSeries x.K)ˣ) : PowerSeries x.K) •
          mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹ := by
      calc (mat x.ρ (h.p₀ g))ᵀ
          = (mat x.ρ (h.p₀ g))ᵀ * (mat x.ρ (G0.frame.conj (h.p₀ g)) * mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹) := by
            rw [hci, mul_one]
        _ = _ := by rw [← mul_assoc, hform, Matrix.smul_mul, one_mul]
    have hu : Units.map (P.f.toRingHom : B →* x.A) (G.frame.eps O B g) = G0.frame.eps ℤ_[l] x.A (h.p₀ g) :=
      Units.ext he
    have hfu : P.f ((G.frame.eps O B g ^ (1 - (n : ℤ)) : Bˣ) : B) =
        ((G0.frame.eps ℤ_[l] x.A (h.p₀ g) ^ (1 - (n : ℤ)) : (x.A)ˣ) : x.A) := by
      calc P.f ((G.frame.eps O B g ^ (1 - (n : ℤ)) : Bˣ) : B)
          = ((Units.map (P.f.toRingHom : B →* x.A) (G.frame.eps O B g ^ (1 - (n : ℤ))) : (x.A)ˣ) : x.A) := rfl
        _ = _ := by rw [map_zpow, hu]
    rw [hrep, hrep, Matrix.transpose_smul, map_mul, hfu, hT, map_inv, hc, mul_smul]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.RepGens

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem conj_prod_zero {R : Type} [CommRing R] {n : ℕ} (w : GL (Fin n) R) (M : Fin n → GL (Fin n) R)
    (c : Fin n → R) (h1 : ∀ k i j, j < i → (w⁻¹ * M k * w : GL (Fin n) R) i j = 0)
    (h2 : ∀ k, (w⁻¹ * M k * w : GL (Fin n) R) k k = c k) :
    (List.ofFn fun k => (M k : Matrix (Fin n) (Fin n) R) - c k • (1 : Matrix (Fin n) (Fin n) R)).prod = 0 := by
  classical
  let f : Matrix (Fin n) (Fin n) R →* Matrix (Fin n) (Fin n) R :=
    { toFun := fun A => (↑w⁻¹ : Matrix (Fin n) (Fin n) R) * A * ↑w
      map_one' := by simp
      map_mul' := fun A B => by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (↑w : Matrix (Fin n) (Fin n) R) (↑w⁻¹ : Matrix (Fin n) (Fin n) R)]
        simp }
  have hf : ∀ k, f ((M k : Matrix (Fin n) (Fin n) R) - c k • (1 : Matrix (Fin n) (Fin n) R)) =
      ((w⁻¹ * M k * w : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - c k • (1 : Matrix (Fin n) (Fin n) R) := by
    intro k
    simp [f, Matrix.mul_sub, Matrix.sub_mul, Units.val_mul]
  have key : f (List.ofFn fun k => (M k : Matrix (Fin n) (Fin n) R) - c k • (1 : Matrix (Fin n) (Fin n) R)).prod = 0 := by
    rw [map_list_prod, List.map_ofFn]
    apply tri_prod_zero
    · intro k i j hij
      simp only [Function.comp_apply, hf, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne (ne_of_lt hij).symm, smul_zero, sub_zero]
      exact h1 k i j hij
    · intro k
      simp only [Function.comp_apply, hf, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      rw [h2 k, sub_self]
  have back : ∀ A : Matrix (Fin n) (Fin n) R,
      A = (↑w : Matrix (Fin n) (Fin n) R) * f A * (↑w⁻¹ : Matrix (Fin n) (Fin n) R) := by
    intro A
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, ← Matrix.mul_assoc]
    simp [Matrix.mul_assoc]
  rw [back (List.ofFn _).prod, key]
  simp

private theorem ch_prod_zero {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c : Fin n → R)
    (h : M.charpoly = ∏ i, (X - C (c i))) :
    (List.ofFn fun k => M - c k • (1 : Matrix (Fin n) (Fin n) R)).prod = 0 := by
  classical
  have e : (List.ofFn fun k => M - c k • (1 : Matrix (Fin n) (Fin n) R)).prod =
      aeval M (∏ i, (X - C (c i))) := by
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    congr 1
    congr 1
    funext k
    simp [Algebra.algebraMap_eq_smul_one]
  rw [e, ← h, aeval_self_charpoly]

theorem UpperTheory.V.Pa.rep_gens :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ z ∈ P.gens, P.rep z = 0 := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P z hz
  have hs : ∀ (g : G.G₀) (b : B), P.rep (MonoidAlgebra.single g b) =
      P.f b • ((x.ρ (h.p₀ g) : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) := by
    intro g b
    simp [OoPt.rep, GDet.repAlg, mat]
  have hfac : ∀ (g : G.G₀) (b : B), P.rep (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 b) =
      ((x.ρ (h.p₀ g) : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) - P.f b • (1 : Matrix (Fin n) (Fin n) x.A) := by
    intro g b
    rw [map_sub, hs, hs]
    simp
  have hst : ∀ y, P.rep y = 0 → P.rep (G.frame.star O B n y) = 0 := by
    intro y hy
    rw [rep_star, hy, Matrix.transpose_zero]
  have hL : ∀ (m : ℕ) (F : Fin m → MonoidAlgebra B G.G₀),
      P.rep (List.ofFn F).prod = (List.ofFn fun i => P.rep (F i)).prod := by
    intro m F
    rw [map_list_prod, List.map_ofFn]
    rfl
  have hφ : ∀ v (g : L.Gv v), h.p₀ (G.frame.φ v g) = G0.frame.φ v g := by
    intro v g
    exact Subtype.ext (h.φ v g)
  have kOrd : ∀ v g, P.rep (G.frame.oEl v (u.ψ v) g) = 0 := by
    intro v g
    rw [GFrame.oEl, hL]
    simp only [hfac]
    apply conj_prod_zero (x.w v) (fun i => x.ρ (h.p₀ (G.frame.φ v (g i)))) (fun i => P.f ↑(u.ψ v i (g i)))
    · intro k i j hij
      rw [hφ]
      exact (x.tri v (g k)).1 i j hij
    · intro k
      rw [hφ, (x.tri v (g k)).2 k, ← P.maps.2 v k]
      rfl
  have kI : ∀ w, ∀ g ∈ r.Ip w, P.rep (MonoidAlgebra.single g 1) = 1 := by
    intro w g hg
    rw [P.Ip w] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    have e : h.p₀ (G.φu w a) = G0.φu w a := Subtype.ext (h.φu w a)
    have hin : G0.φu w a ∈ G0.frame.Iu w := ⟨a, ha, rfl⟩
    rw [hs, e, x.ine w _ hin]
    simp
  have kq1 : ∀ j, P.rep (q1El (P.ph j) (P.U j)) = 0 := by
    intro j
    rw [q1El, hL]
    simp only [hfac]
    exact ch_prod_zero _ _ (P.eig j)
  have kq2 : ∀ j i, P.rep (q2El (P.ph j) (P.ta j) (P.U j) i (P.y j i)) = 0 := by
    intro j i
    rw [q2El, map_mul, map_sub, map_sub, hs, hs, P.p_ta j, P.f_y j i]
    simp
  rcases hz with hz | hz
  · rcases hz with ⟨v, g, rfl | rfl⟩ | ⟨w, g, hg, rfl | rfl⟩
    · exact kOrd v g
    · exact hst _ (kOrd v g)
    · rw [map_sub, kI w g hg, map_one, sub_self]
    · rw [map_sub, rep_star, kI w g hg, map_one, Matrix.transpose_one, sub_self]
  · rcases hz with ⟨j, rfl | rfl⟩ | ⟨j, i, rfl | rfl⟩
    · exact kq1 j
    · exact hst _ (kq1 j)
    · exact kq2 j i
    · exact hst _ (kq2 j i)
end
end
