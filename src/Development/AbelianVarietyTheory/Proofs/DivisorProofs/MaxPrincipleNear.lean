module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousReadOnAffineOpenRingHoms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMaximumPrincipleWeightFiniteMvPolynomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousReadOnAffineOpenRingHomsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.exists_continuous_read_on_affineOpen_ringHoms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (U : X.Opens) (hU : IsAffineOpen U) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ), (∀ σ, ContinuousOn (u σ) (ptsIn p σ U)) → (letI : TopologicalSpace (Γ(X, U) →+* ℂ) := TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance; ∃ ψ : (Γ(X, U) →+* ℂ) → ℝ, Continuous ψ ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), ψ (evHom hy) = u σ y) ∧ (∀ x : Γ(X, U) →+* ℂ, ∃ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), evHom hy = x) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U) (W : Set (Γ(X, U) →+* ℂ)), W ∈ 𝓝 (evHom hy) → {z : CxPts p σ | ∃ hz : z ∈ ptsIn p σ U, evHom hz ∈ W} ∈ 𝓝 y) := by
  first | exact @GlobalTheory.ContRead.exists_continuous_read | exact GlobalTheory.ContRead.exists_continuous_read | (intros; apply GlobalTheory.ContRead.exists_continuous_read <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFramesStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.hermLineBundlePairNorm_independent_of_frames : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∀ (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (P.L.B.U i) → y ∈ ptsIn p σ (P.A.B.U j) → P.nu a b σ y f = ‖ratVal (P.loc a b f i j) y‖ * Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) := by
  first | exact @GlobalTheory.VolBr.nu_eq | exact GlobalTheory.VolBr.nu_eq | (intros; apply GlobalTheory.VolBr.nu_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMaximumPrincipleWeightFiniteMvPolynomialStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.local_maximum_principle_weight_finite_mvPolynomial : ∀ (d : ℕ) (B : Type) [CommRing B] [IsDomain B] [Algebra (MvPolynomial (Fin d) ℚ) B] [Module.Finite (MvPolynomial (Fin d) ℚ) B], Function.Injective (algebraMap (MvPolynomial (Fin d) ℚ) B) → (letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance; ∀ (ψ : (B →+* ℂ) → ℝ), Continuous ψ → ∀ s : B, s ≠ 0 → ∀ (x₀ : B →+* ℂ) (δ : ℝ), 0 < δ → ∃ (W K : Set (B →+* ℂ)), W ∈ nhds x₀ ∧ IsCompact K ∧ (∀ x ∈ K, x s ≠ 0) ∧ ∀ (N : ℕ) (f : B) (R : ℝ), (∀ x ∈ K, ‖x f‖ * Real.exp (-(N * ψ x)) ≤ R) → ∀ y ∈ W, ‖y f‖ * Real.exp (-(N * ψ y)) ≤ Real.exp (δ * N) * R) := by
  first | exact @GlobalTheory.local_maximum_principle_weight_finite_mvPolynomial_algebra | exact GlobalTheory.local_maximum_principle_weight_finite_mvPolynomial_algebra | (intros; apply GlobalTheory.local_maximum_principle_weight_finite_mvPolynomial_algebra <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMaxPrincipleWeightedFiniteTypeInt

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory

theorem isLocalization_rat_tensor (B : Type) [CommRing B] :
    letI := Algebra.TensorProduct.rightAlgebra (R := ℤ) (A := ℚ) (B := B);
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)) (ℚ ⊗[ℤ] B) :=
  IsLocalization.tensorRight ℚ (nonZeroDivisors ℤ)

theorem intMap_le_nonZeroDivisors (B : Type) [CommRing B] [IsDomain B] [CharZero B] :
    Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ) ≤ nonZeroDivisors B := by
  rintro _ ⟨n, hn, rfl⟩
  have h : n ≠ 0 := nonZeroDivisors.ne_zero hn
  exact mem_nonZeroDivisors_of_ne_zero (by simpa using h)

noncomputable def ratExtPoint {B : Type} [CommRing B] (x : B →+* ℂ) : ℚ ⊗[ℤ] B →+* ℂ :=
  (Algebra.TensorProduct.lift (algebraMap ℚ ℂ).toIntAlgHom x.toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

theorem ratExtPoint_tmul {B : Type} [CommRing B] (x : B →+* ℂ) (q : ℚ) (b : B) :
    ratExtPoint x (q ⊗ₜ[ℤ] b) = (q : ℂ) * x b := by
  simp [ratExtPoint]

theorem local_max_principle_int : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B], (letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance; ∀ (ψ : (B →+* ℂ) → ℝ), Continuous ψ → ∀ s : B, s ≠ 0 → ∀ (x₀ : B →+* ℂ) (δ : ℝ), 0 < δ → ∃ (W K : Set (B →+* ℂ)), W ∈ nhds x₀ ∧ IsCompact K ∧ (∀ x ∈ K, x s ≠ 0) ∧ ∀ (N : ℕ) (f : B) (R : ℝ), (∀ x ∈ K, ‖x f‖ * Real.exp (-(N * ψ x)) ≤ R) → ∀ y ∈ W, ‖y f‖ * Real.exp (-(N * ψ y)) ≤ Real.exp (δ * N) * R) := by
  intro B _ _ _ _
  letI tB : TopologicalSpace (B →+* ℂ) :=
    TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance
  intro ψ hψ s hs x₀ δ hδ
  letI := Algebra.TensorProduct.rightAlgebra (R := ℤ) (A := ℚ) (B := B)
  haveI := isLocalization_rat_tensor B
  have hle := intMap_le_nonZeroDivisors B
  haveI : IsDomain (ℚ ⊗[ℤ] B) := IsLocalization.isDomain_of_le_nonZeroDivisors (ℚ ⊗[ℤ] B) hle
  have hinj : Function.Injective (algebraMap B (ℚ ⊗[ℤ] B)) := IsLocalization.injective _ hle
  set φ : B →+* ℚ ⊗[ℤ] B := algebraMap B (ℚ ⊗[ℤ] B) with hφ
  have hφ' : ∀ b, φ b = (1 : ℚ) ⊗ₜ[ℤ] b := fun _ => rfl
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg ℚ (ℚ ⊗[ℤ] B)
  letI : Algebra (MvPolynomial (Fin d) ℚ) (ℚ ⊗[ℤ] B) := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin d) ℚ) (ℚ ⊗[ℤ] B) := hfin
  letI tB' : TopologicalSpace (ℚ ⊗[ℤ] B →+* ℂ) :=
    TopologicalSpace.induced (fun x : ℚ ⊗[ℤ] B →+* ℂ => (x : ℚ ⊗[ℤ] B → ℂ)) inferInstance
  have hev : ∀ b : B, Continuous fun x : B →+* ℂ => x b := fun b =>
    (continuous_apply b).comp continuous_induced_dom
  have hev' : ∀ b : ℚ ⊗[ℤ] B, Continuous fun x : ℚ ⊗[ℤ] B →+* ℂ => x b := fun b =>
    (continuous_apply b).comp continuous_induced_dom
  have hres : Continuous fun x : ℚ ⊗[ℤ] B →+* ℂ => x.comp φ :=
    continuous_induced_rng.2 (continuous_pi fun b => hev' (φ b))
  have hext : Continuous fun x : B →+* ℂ => ratExtPoint x := by
    refine continuous_induced_rng.2 (continuous_pi fun t => ?_)
    change Continuous fun x : B →+* ℂ => ratExtPoint x t
    induction t using TensorProduct.induction_on with
    | zero => simpa using continuous_const
    | tmul q b => simp only [ratExtPoint_tmul]; exact continuous_const.mul (hev b)
    | add t u ht hu => simp only [map_add (f := _)]; exact ht.add hu
  have hcomp : ∀ x : B →+* ℂ, (ratExtPoint x).comp φ = x := fun x => by
    ext b
    simp [hφ', ratExtPoint_tmul]
  obtain ⟨W, K, hW, hK, hKs, hb⟩ := GlobalTheory.T.local_maximum_principle_weight_finite_mvPolynomial d (ℚ ⊗[ℤ] B) hg (fun x => ψ (x.comp φ))
    (hψ.comp hres) (φ s) (fun h => hs (hinj (h.trans (map_zero _).symm))) (ratExtPoint x₀) δ hδ
  refine ⟨(fun x => ratExtPoint x) ⁻¹' W, (fun x => x.comp φ) '' K,
    hext.continuousAt.preimage_mem_nhds hW, hK.image hres, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hKs x hx
  · intro N f R hR y hy
    have h := hb N (φ f) R (fun x hx => hR _ ⟨x, hx, rfl⟩) (ratExtPoint y) hy
    have h2 : ratExtPoint y (φ f) = y f := by rw [← RingHom.comp_apply, hcomp]
    simpa only [hcomp, h2] using h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMaxPrincipleWeightedFiniteTypeIntStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.local_max_principle_weighted_finiteType_int : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B], (letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance; ∀ (ψ : (B →+* ℂ) → ℝ), Continuous ψ → ∀ s : B, s ≠ 0 → ∀ (x₀ : B →+* ℂ) (δ : ℝ), 0 < δ → ∃ (W K : Set (B →+* ℂ)), W ∈ nhds x₀ ∧ IsCompact K ∧ (∀ x ∈ K, x s ≠ 0) ∧ ∀ (N : ℕ) (f : B) (R : ℝ), (∀ x ∈ K, ‖x f‖ * Real.exp (-(N * ψ x)) ≤ R) → ∀ y ∈ W, ‖y f‖ * Real.exp (-(N * ψ y)) ≤ Real.exp (δ * N) * R) := by
  first | exact @GlobalTheory.local_max_principle_int | exact GlobalTheory.local_max_principle_int | (intros; apply GlobalTheory.local_max_principle_int <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxPrincipleNear

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem finiteType_int_of_isAffineOpen {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  obtain ⟨N, i, hi, e⟩ := hX.isProjOver
  have : LocallyOfFiniteType p := by subst e; infer_instance
  have : Module.Finite ℤ k := hX.finite
  have h1 := Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp k)) hU (by simp)
  have h2 : (algebraMap ℤ k).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
  have h3 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).FiniteType :=
    RingHom.FiniteType.of_surjective _ fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom x, by simp⟩
  have h4 := h1.comp (h3.comp h2)
  rw [← RingHom.finiteType_algebraMap]
  convert h4 using 1
  exact RingHom.ext_int _ _

theorem Pair.max_principle_near : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∀ (σ : k →+* ℂ) (y₀ : CxPts p σ), ∃ (W : Set (CxPts p σ)) (ρ : ℝ), W ∈ 𝓝 y₀ ∧ 0 < ρ ∧ ∀ (N : ℕ) (f : X.functionField) (R : ℝ), f ∈ P.H N 0 → (∀ (σ' : k →+* ℂ) (y : CxPts p σ'), ρ ≤ P.nu 0 1 σ' y s → P.nu N 0 σ' y f ≤ R) → ∀ y ∈ W, P.nu N 0 σ y f ≤ Real.exp (δ * N) * R := by
  intro k _ X _ p D hX P s hs hs0 δ hδ σ y₀
  set i := pick (P.L.φ σ).isLB y₀
  set j := pick (P.A.φ σ).isLB y₀
  have hyi : y₀ ∈ ptsIn p σ (P.L.B.U i) := mem_pick _ _
  have hyj : y₀ ∈ ptsIn p σ (P.A.B.U j) := mem_pick _ _
  have hxV : y₀.1 (IsLocalRing.closedPoint ℂ) ∈ P.L.B.U i ⊓ P.A.B.U j :=
    GlobalTheory.CxPts.mem_ptsIn.1 (GlobalTheory.CxPts.mem_ptsIn_inf.2 ⟨hyi, hyj⟩)
  obtain ⟨U, hUa, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxV
  have hUi : U ≤ P.L.B.U i := hUV.trans inf_le_left
  have hUj : U ≤ P.A.B.U j := hUV.trans inf_le_right
  have hy₀U : y₀ ∈ ptsIn p σ U := GlobalTheory.CxPts.mem_ptsIn.2 hxU
  have hgen : genericPoint X ∈ U := gen_mem hxU
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : CharZero Γ(X, U) := RingHom.charZero (evHom hy₀U)
  have : Algebra.FiniteType ℤ Γ(X, U) := finiteType_int_of_isAffineOpen hX hUa
  let _ : TopologicalSpace (Γ(X, U) →+* ℂ) :=
    TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance
  have hcont : ∀ (M : HermLB p) (c : M.B.ι), U ≤ M.B.U c → ∀ σ' : k →+* ℂ,
      ContinuousOn (fun y => (M.φ σ').φ c y / 2) (ptsIn p σ' U) := by
    intro M c hc σ' y hy
    exact ((M.cInf σ' c y (ptsIn_mono hc hy)).continuousAt.div_const 2).continuousWithinAt
  obtain ⟨ψ, hψc, hψv, hsurj, hnb⟩ :=
    GlobalTheory.T.exists_continuous_read_on_affineOpen_ringHoms k X p D hX U hUa (fun σ' y => (P.L.φ σ').φ i y / 2) (hcont P.L i hUi)
  obtain ⟨ψ', hψ'c, hψ'v, -, -⟩ :=
    GlobalTheory.T.exists_continuous_read_on_affineOpen_ringHoms k X p D hX U hUa (fun σ' y => (P.A.φ σ').φ j y / 2) (hcont P.A j hUj)
  have hsreg : ∀ x ∈ U, RegAt x (P.loc 0 1 s i j) := fun x hx => hs x i j (hUi hx) (hUj hx)
  obtain ⟨s', hs'⟩ := exists_fnOf_eq hgen hsreg
  have hs'0 : s' ≠ 0 := by
    rintro rfl
    simp [Pair.loc, hs0] at hs'
  obtain ⟨W', K, hW', hK, hKs, hmain⟩ := GlobalTheory.T.local_max_principle_weighted_finiteType_int Γ(X, U) ψ hψc s' hs'0 (evHom hy₀U) δ hδ
  have hgc : Continuous (fun x : Γ(X, U) →+* ℂ => ‖x s'‖ * Real.exp (-ψ' x)) :=
    (((continuous_apply s').comp continuous_induced_dom).norm).mul (Real.continuous_exp.comp hψ'c.neg)
  obtain ⟨ρ, hρ, hρK⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ρ ≤ ‖x s'‖ * Real.exp (-ψ' x) := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, by simp [hKe]⟩
    · obtain ⟨x₁, hx₁, hmin⟩ := hK.exists_isMinOn hKne hgc.continuousOn
      exact ⟨_, mul_pos (norm_pos_iff.2 (hKs x₁ hx₁)) (Real.exp_pos _), fun x hx => isMinOn_iff.mp hmin x hx⟩
  refine ⟨{z | ∃ hz : z ∈ ptsIn p σ U, evHom hz ∈ W'}, ρ, hnb σ y₀ hy₀U W' hW', hρ, ?_⟩
  intro N f R hf hR y hyW
  obtain ⟨hyU, hyW'⟩ := hyW
  have hfreg : ∀ x ∈ U, RegAt x (P.loc N 0 f i j) := fun x hx => hf x i j (hUi hx) (hUj hx)
  obtain ⟨f', hf'⟩ := exists_fnOf_eq hgen hfreg
  have hnuF : ∀ (σ' : k →+* ℂ) (z : CxPts p σ') (hz : z ∈ ptsIn p σ' U),
      P.nu N 0 σ' z f = ‖evHom hz f'‖ * Real.exp (-(N * ψ (evHom hz))) := by
    intro σ' z hz
    rw [GlobalTheory.T.hermLineBundlePairNorm_independent_of_frames k X p P N 0 f hf σ' z i j (ptsIn_mono hUi hz) (ptsIn_mono hUj hz), ← hf',
      ratVal_fnOf hz hgen, ev_eq hz, hψv σ' z hz]
    congr 2
    push_cast
    ring
  have hnuS : ∀ (σ' : k →+* ℂ) (z : CxPts p σ') (hz : z ∈ ptsIn p σ' U),
      P.nu 0 1 σ' z s = ‖evHom hz s'‖ * Real.exp (-ψ' (evHom hz)) := by
    intro σ' z hz
    rw [GlobalTheory.T.hermLineBundlePairNorm_independent_of_frames k X p P 0 1 s hs σ' z i j (ptsIn_mono hUi hz) (ptsIn_mono hUj hz), ← hs',
      ratVal_fnOf hz hgen, ev_eq hz, hψ'v σ' z hz]
    congr 2
    push_cast
    ring
  rw [hnuF σ y hyU]
  refine hmain N f' R ?_ (evHom hyU) hyW'
  intro x hx
  obtain ⟨σ', z, hz, rfl⟩ := hsurj x
  rw [← hnuF σ' z hz]
  exact hR σ' z (by rw [hnuS σ' z hz]; exact hρK _ hx)

end GlobalTheory.VolBr
end
end
