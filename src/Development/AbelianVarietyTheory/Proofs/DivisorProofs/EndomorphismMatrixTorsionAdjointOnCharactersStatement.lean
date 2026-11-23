module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenMap
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelCongruenceEndoAllAlgClosedFields
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTauLineBundleCoordinateEqExpStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdjointApplyOfWeightedQuadraticSumPolar

section

@[expose] public section

open GlobalTheory.Poinc Matrix

namespace GlobalTheory.Poinc

theorem qW_polar_eq_sum_add_transpose {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (hβ : ∀ a b, β a b = β b a) (y z : Fin s → X) :
    qW W β (y + z) - qW W β y - qW W β z = ∑ u, ∑ v, (W + W.transpose) u v * β (y u) (z v) := by
  have h : ∑ u, ∑ v, W u v * β (z u) (y v) = ∑ u, ∑ v, W v u * β (y u) (z v) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hβ]
  simp only [qW, Pi.add_apply, map_add (f := _), LinearMap.add_apply, mul_add, add_mul, Finset.sum_add_distrib,
    Matrix.add_apply, Matrix.transpose_apply, h]
  ring

theorem eq_adjoint_apply_of_qW_polar (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : PosW W) (X₀ : Type) [AddCommGroup X₀]
    (β : LinearMap.BilinForm ℤ X₀) (hβ : ∀ a b, β a b = β b a) (hpos : ∀ a, a ≠ 0 → 0 < β a a)
    (E E' : Matrix (Fin 8) (Fin 8) ℤ) (hE : (W + W.transpose) * E' = E.transpose * (W + W.transpose))
    (z z' : Fin 8 → X₀)
    (h : ∀ y : Fin 8 → X₀, qW W β ((fun a => ∑ b, E a b • y b) + z) - qW W β (fun a => ∑ b, E a b • y b) - qW W β z =
      qW W β (y + z') - qW W β y - qW W β z') :
    z' = fun a => ∑ b, E' a b • z b := by
  simp only [qW_polar_eq_sum_add_transpose W β hβ] at h
  unfold PosW at hW
  set M := W + W.transpose with hM
  have hdet : M.det ≠ 0 := by
    have h1 := hW.det_pos
    have h2 : (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := by
      rw [Int.cast_det]
    rw [h2] at h1
    intro h0
    simp [h0] at h1
  have key : ∀ x : X₀, (fun v => β x (z' v)) = E' *ᵥ (fun v => β x (z v)) := by
    intro x
    rw [← sub_eq_zero]
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hE, sub_eq_zero]
    funext w
    have h1 := h (Pi.single w x)
    have h2 : ∀ a, ∑ b, E a b • (Pi.single w x : Fin 8 → X₀) b = E a w • x := by
      intro a
      rw [Finset.sum_eq_single w] <;> simp +contextual [Pi.single_apply]
    have h3 : ∑ u, ∑ v, M u v * β ((Pi.single w x : Fin 8 → X₀) u) (z' v) = ∑ v, M w v * β x (z' v) := by
      rw [Finset.sum_eq_single w] <;> simp +contextual [Pi.single_apply]
    simp only [h2, h3, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h1
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [← h1, Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  funext a
  rw [← sub_eq_zero]
  by_contra hne
  have h1 := hpos _ hne
  generalize hd : z' a - ∑ b, E' a b • z b = d at h1
  have h2 := congrFun (key d) a
  have h3 : β d d = 0 := by
    conv_lhs => rw [show β d d = β d (z' a - ∑ b, E' a b • z b) by rw [hd]]

    simp only [map_sub, map_sum, map_zsmul, smul_eq_mul, h2, Matrix.mulVec, dotProduct, sub_self]
  omega

end GlobalTheory.Poinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdjointApplyOfWeightedQuadraticSumPolarStatement

section

@[expose] public section

open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.eq_adjoint_apply_of_weightedQuadraticSum_polar : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (X₀ : Type) [AddCommGroup X₀] (β : LinearMap.BilinForm ℤ X₀), (∀ a b, β a b = β b a) → (∀ a, a ≠ 0 → 0 < β a a) → ∀ (E E' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * E' = E.transpose * (W + W.transpose) → ∀ z z' : Fin 8 → X₀, (∀ y : Fin 8 → X₀, qW W β ((fun a => ∑ b, E a b • y b) + z) - qW W β (fun a => ∑ b, E a b • y b) - qW W β z = qW W β (y + z') - qW W β y - qW W β z') → z' = fun a => ∑ b, E' a b • z b := by
  first | exact @GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar | exact GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar | (intros; apply GlobalTheory.Poinc.eq_adjoint_apply_of_qW_polar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelCongruenceEndoAllAlgClosedFieldsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

theorem _root_.GlobalTheory.T.labelCongruence_endo_all_algClosed_fields : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (eA : u.A.A ⟶ u.A.A) (s : u.D.toPre.X →+ u.D.toPre.X), (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left = x.left ≫ eA.left → CongMod m pk'.y (s pk.y)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing u.V) F] (k : ℕ), 1 ≤ k → IsUnit (k : u.V) → ∀ (q q' : QkPt u.D.toPre F k) (a a' : TFK (R := u.V) F ⟶ u.A.A), QkToAkU u.U.toUnifPre F k q a → QkToAkU u.U.toUnifPre F k q' a' → a.left = a'.left ≫ eA.left → CongMod k q.y (s q'.y) := by
  first | exact @GlobalTheory.LabelTransfer.main | exact GlobalTheory.LabelTransfer.main | (intros; apply GlobalTheory.LabelTransfer.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismMatrixTorsionAdjointOnCharacters

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section
namespace GlobalTheory.Poinc.FibMatrix

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (X₀ : Type) [AddCommGroup X₀] (β : LinearMap.BilinForm ℤ X₀), (∀ a b, β a b = β b a) → (∀ a, a ≠ 0 → 0 < β a a) → ∀ sc : ℝ, 0 < sc → ∀ j : u.D.toPre.X ≃+ (Fin 8 → X₀), (∀ χ, l.q χ = sc * (qW W β (j χ) : ℤ)) → ∀ (e : ρ.P.A ⟶ ρ.P.A) (E E' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * E' = E.transpose * (W + W.transpose) → (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ e.left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)) → ∀ (F : u.G ⟶ u.G) (eA : u.A.A ⟶ u.A.A), IsMonHom F → eA.left ≫ u.φ = u.φ ≫ e.left → eA.left ≫ genMap u.U = genMap u.U ≫ F.left → ∀ m : u.D.toPre.X →+ u.D.toPre.X, EndChar u.U F m → ∀ χ, j (m χ) = fun a => ∑ b, E' a b • j χ b := by
  intro o Ω _ _ _ S ρ p _ y₀ u l W hW X₀ _ β hβs hβp sc hsc j hq e E E' hEE hlab F eA hF heA hgen m hm χ
  have hCZ : CharZero u.V :=
    RingHom.charZero ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hBase : GlobalTheory.Mum.Base u.V := ⟨⟨inferInstance, inferInstance, inferInstance, u.complete⟩, hCZ⟩
  let Em : (Fin 8 → X₀) →+ (Fin 8 → X₀) :=
    { toFun := fun y a => ∑ b, E a b • y b
      map_zero' := by ext; simp
      map_add' := fun y y' => by ext; simp [smul_add, Finset.sum_add_distrib] }
  have hEm : ∀ y, Em y = fun a => ∑ b, E a b • y b := fun _ => rfl
  let s : u.D.toPre.X →+ u.D.toPre.X := (j.symm.toAddMonoidHom.comp Em).comp j.toAddMonoidHom
  have hs : ∀ x, j (s x) = Em (j x) := fun x => by simp [s]
  have hlab' : ∀ (k : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) k) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A),
      1 ≤ k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk' x' →
      x'.left = x.left ≫ eA.left → CongMod k pk'.y (s pk.y) := by
    intro k pk pk' x x' hk hx hx' hxx
    obtain ⟨w, hw⟩ := hlab k pk pk' x x' hk hx hx' (by rw [hxx, Category.assoc, heA])
    refine ⟨j.symm w, j.injective ?_⟩
    rw [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, hs, hw, hEm]
  have hT := GlobalTheory.T.labelCongruence_endo_all_algClosed_fields o Ω S ρ p y₀ u eA s hlab'
  haveI : Mono (jK u.V) := GlobalTheory.PolDeg.Wit.mono_jK
  haveI : Mono (genMap u.U) := by unfold genMap; infer_instance
  have hTor := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar u.V hBase u.G u.semi u.D u.A u.U F hF m hm
  have hmain := GlobalTheory.TauFormHom.main u.V hBase inferInstance u.G u.semi u.D u.A u.U u.G u.semi u.D u.A u.U F hF m s hTor
    (by
      intro F' _ _ _ k hk q q' a a' hqa hqa' haa
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hk)
      have ha : a.left = a'.left ≫ eA.left := by
        rw [← cancel_mono (genMap u.U), haa, Category.assoc, hgen]
      exact hT F' k hk1 hk q q' a a' hqa hqa' ha)
  have hunit : ∀ w : u.Vˣ, ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V))‖ = 1 := by
    intro w
    have h1 := (u.norm_le (algebraMap u.V _ (w : u.V))).2 ⟨w, rfl⟩
    have h2 := (u.norm_le (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V))).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V))‖ *
        ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    have h4 := norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((w⁻¹ : u.Vˣ) : u.V)))
    have h5 := norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (w : u.V)))
    nlinarith
  have hpol : ∀ a' b, l.q (s a' + b) - l.q (s a') - l.q b = l.q (a' + m b) - l.q a' - l.q (m b) := by
    intro a' b
    obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord u.V u.D.toPre (s a') b
    obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord u.V u.D.toPre a' (m b)
    obtain ⟨w, hw⟩ := hmain a' b x x' hx hx'
    have n₁ := GlobalTheory.T.norm_tauLineBundleCoordinate_eq_exp o Ω S ρ p y₀ u l (s a') b x hx
    have n₂ := GlobalTheory.T.norm_tauLineBundleCoordinate_eq_exp o Ω S ρ p y₀ u l a' (m b) x' hx'
    rw [hw, map_mul, norm_mul, hunit, _root_.one_mul, n₂] at n₁
    have := Real.exp_injective n₁
    linarith
  have hpolW : ∀ y : Fin 8 → X₀, qW W β ((fun a => ∑ b, E a b • y b) + j χ) - qW W β (fun a => ∑ b, E a b • y b) -
      qW W β (j χ) = qW W β (y + j (m χ)) - qW W β y - qW W β (j (m χ)) := by
    intro y
    have h := hpol (j.symm y) χ
    rw [hq, hq, hq, hq, hq, hq, map_add (f := _), map_add (f := _), hs, AddEquiv.apply_symm_apply, hEm] at h
    have h' : sc * ((qW W β ((fun a => ∑ b, E a b • y b) + j χ) - qW W β (fun a => ∑ b, E a b • y b) -
        qW W β (j χ) : ℤ) : ℝ) = sc * ((qW W β (y + j (m χ)) - qW W β y - qW W β (j (m χ)) : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast mul_left_cancel₀ hsc.ne' h'
  exact GlobalTheory.T.eq_adjoint_apply_of_weightedQuadraticSum_polar W hW X₀ β hβs hβp E E' hEE (j χ) (j (m χ)) hpolW

end GlobalTheory.Poinc.FibMatrix
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismMatrixTorsionAdjointOnCharactersStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8


theorem _root_.GlobalTheory.T.endomorphism_matrix_torsion_adjoint_on_characters : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (X₀ : Type) [AddCommGroup X₀] (β : LinearMap.BilinForm ℤ X₀), (∀ a b, β a b = β b a) → (∀ a, a ≠ 0 → 0 < β a a) → ∀ sc : ℝ, 0 < sc → ∀ j : u.D.toPre.X ≃+ (Fin 8 → X₀), (∀ χ, l.q χ = sc * (qW W β (j χ) : ℤ)) → ∀ (e : ρ.P.A ⟶ ρ.P.A) (E E' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * E' = E.transpose * (W + W.transpose) → (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ e.left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)) → ∀ (F : u.G ⟶ u.G) (eA : u.A.A ⟶ u.A.A), IsMonHom F → eA.left ≫ u.φ = u.φ ≫ e.left → eA.left ≫ genMap u.U = genMap u.U ≫ F.left → ∀ m : u.D.toPre.X →+ u.D.toPre.X, EndChar u.U F m → ∀ χ, j (m χ) = fun a => ∑ b, E' a b • j χ b := by
  first | exact @GlobalTheory.Poinc.FibMatrix.main | exact GlobalTheory.Poinc.FibMatrix.main | (intros; apply GlobalTheory.Poinc.FibMatrix.main <;> assumption)
end
end
