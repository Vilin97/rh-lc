module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicFrameTorusElementMatrixEqStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealIdeleFlow

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResLine

theorem exists_real_idele_flow (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ l : ℝ → (AF F ⊗[F] E)ˣ, Continuous l ∧ (∀ s t, l (s + t) = l s * l t) ∧
      (∀ t, sigR (AF F) σ (l t).1 = (l t).1) ∧ ∀ t, (absE F E (l t) : ℝ) = Real.exp t := by
  have := h.1
  let e := fun w : InfinitePlace F => InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)
  let ρ : ℝ →* AF F :=
    { toFun := fun x => ((fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm x :
        Ainf F), (1 : Af F))
      map_one' := Prod.ext (funext fun w => map_one _) rfl
      map_mul' := fun x y => Prod.ext (funext fun w => map_mul _ _ _) (mul_one _).symm }
  have hρ : Continuous ρ := (continuous_pi fun w => (e w).symm.continuous).prodMk continuous_const
  have hn : ∀ w x, ‖evInf F w (ρ x)‖ = ‖x‖ := fun w x =>
    (e w).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm) x
  let ι : AF F →* AF F ⊗[F] E := (algebraMap (AF F) (AF F ⊗[F] E)).toMonoidHom
  have hι : Continuous ι := by
    haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
    exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  let d : ℕ := Fintype.card (InfinitePlace F)
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let u : ℝ → ℝˣ := fun t => Units.mk0 (Real.exp (t / (2 * d))) (Real.exp_ne_zero _)
  have hu : Continuous u := Units.continuous_iff.2
    ⟨show Continuous fun t : ℝ => Real.exp (t / (2 * d)) by fun_prop,
      show Continuous fun t : ℝ => (Real.exp (t / (2 * d)))⁻¹ from
        Continuous.inv₀ (by fun_prop) fun _ => Real.exp_ne_zero _⟩
  refine ⟨fun t => Units.map (ι.comp ρ) (u t), (Continuous.units_map (ι.comp ρ) (show Continuous (ι ∘ ρ) from hι.comp hρ)).comp hu, fun s t => ?_,
    fun t => congrArg (ρ (u t) ⊗ₜ[F] ·) (map_one σ), fun t => ?_⟩
  · rw [← map_mul]
    exact congrArg _ (Units.ext (show Real.exp _ = Real.exp _ * Real.exp _ by rw [← Real.exp_add, add_div]))
  · have h1 : Algebra.norm (AF F) (Units.map (ι.comp ρ) (u t)).1 = ρ (u t) ^ 2 := by
      change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (ρ (u t))) = _
      haveI : Nontrivial (AF F) := (evInf F (Classical.arbitrary _)).toRingHom.domain_nontrivial
      rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h.2.2.1]
    have h2 : ∀ v, evFin F v (ρ (u t)) = 1 := fun v => rfl
    have h3 : ∀ w : InfinitePlace F, w.mult = 1 := fun w => if_pos (IsTotallyReal.isReal w)
    simp only [GlobalTheory.Doubling.absE_apply, GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf, h1, map_pow, h2, h3,
      one_pow, nnnorm_one, finprod_one, mul_one, pow_one, NNReal.coe_prod, coe_nnnorm, norm_pow, hn,
      Finset.prod_const, Finset.card_univ]
    change (‖Real.exp (t / (2 * d))‖ ^ 2) ^ d = _
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← pow_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp

end GlobalTheory.ResLine
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMul

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus
theorem isIdTorusElt_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {l l' : Fin r → (AF F ⊗[F] E)ˣ} {a b : GAd σ J}
    (ha : IsIdTorusElt σ J X Y l a) (hb : IsIdTorusElt σ J X Y l' b) : IsIdTorusElt σ J X Y (l * l') (a * b) := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  refine ⟨?_, ?_, fun z hz => ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb1, ← Matrix.mul_assoc, ha1, Matrix.mul_assoc, diagonal_mul_diagonal]
    exact congrArg _ (congrArg _ (funext fun k => by simp))
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb2, ← Matrix.mul_assoc, ha2, Matrix.mul_assoc, diagonal_mul_diagonal]
    exact congrArg _ (congrArg _ (funext fun k => by simp [map_mul, mul_inv, Units.val_mul, mul_comm]))
  · rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hb3 z hz, ha3 z hz]
end GlobalTheory.IdTorus
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementUnique

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorus

theorem idelicFrameTorusElement_apply_column_decomposition {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J} (ha : IsIdTorusElt σ J X Y l a) (z : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J a).1 *ᵥ z =
      adMat F X *ᵥ (diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) *ᵥ
          (adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z)) +
      adMat F Y *ᵥ (diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) *ᵥ
          (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z)) +
      (z - adMat F X *ᵥ (adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z)
         - adMat F Y *ᵥ (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z)) := by
  set P := adMat F (Formalism.UG.cT (σ : E →+* E) X * J)
  set Q := adMat F (Formalism.UG.cT (σ : E →+* E) Y * J)
  have mm : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E),
      adMat F A * adMat F B = adMat F (A * B) := fun A B => (Matrix.map_mul).symm
  have hPX : P * adMat F X = 0 := by rw [mm, hW.xx]; simp
  have hPY : P * adMat F Y = 1 := by rw [mm, hW.xy]; simp
  have hQX : Q * adMat F X = 1 := by rw [mm, yx h hJ hW]; simp
  have hQY : Q * adMat F Y = 0 := by rw [mm, hW.yy]; simp
  set w := z - adMat F X *ᵥ (Q *ᵥ z) - adMat F Y *ᵥ (P *ᵥ z) with hw
  have hPw : P *ᵥ w = 0 := by
    rw [hw, mulVec_sub, mulVec_sub, mulVec_mulVec (M := P) (N := adMat F X), mulVec_mulVec (M := P) (N := adMat F Y), hPX, hPY,
      zero_mulVec, one_mulVec]; simp
  have hQw : Q *ᵥ w = 0 := by
    rw [hw, mulVec_sub, mulVec_sub, mulVec_mulVec (M := Q) (N := adMat F X), mulVec_mulVec (M := Q) (N := adMat F Y), hQX, hQY,
      zero_mulVec, one_mulVec]; simp
  have hmem : w ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ := by
    refine ⟨(Submodule.mem_iInf _).2 fun i => (Submodule.mem_iInf _).2 fun _ => LinearMap.mem_ker.2 ?_,
      (Submodule.mem_iInf _).2 fun i => (Submodule.mem_iInf _).2 fun _ => LinearMap.mem_ker.2 ?_⟩
    · exact congrFun hPw i
    · exact congrFun hQw i
  have hz : z = adMat F X *ᵥ (Q *ᵥ z) + adMat F Y *ᵥ (P *ᵥ z) + w := by rw [hw]; abel
  conv_lhs => rw [hz]
  rw [mulVec_add, mulVec_add, mulVec_mulVec (N := adMat F X), mulVec_mulVec (N := adMat F Y), ha.1, ha.2.1,
    ha.2.2 w hmem, ← mulVec_mulVec, ← mulVec_mulVec]

theorem isIdTorusElt_uniq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a b : GAd σ J}, IsIdTorusElt σ J X Y l a → IsIdTorusElt σ J X Y l b → a = b := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW l a b ha hb
  apply matHom_injective (AF F) σ J
  apply Units.ext
  have hv : ∀ z, (matHom _ σ J a).1 *ᵥ z = (matHom _ σ J b).1 *ᵥ z := fun z => by
    rw [idelicFrameTorusElement_apply_column_decomposition h hJ hW ha, idelicFrameTorusElement_apply_column_decomposition h hJ hW hb]
  ext i j
  simpa [mulVec_single_one] using congrFun (hv (Pi.single j 1)) i

end GlobalTheory.IdTorus

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusInLeviParabolic

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorusCent

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem swap (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : IsWittFrame σ J Y X :=
  ⟨hW.yy, hW.xx, yx h hJ hW, fun z h1 h2 h3 => hW.aniso z h2 h1 h3⟩

end GlobalTheory.IdTorusCent

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviCentreFlowWittFrame

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResidueFlow

open Matrix GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (conjUnit)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem row_of_stab {X Y : Matrix (Fin n) (Fin r) E} (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {g : GAd σ J} {B C : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    (hX : (matHom _ σ J g).1 * adMat F X = adMat F X * B) (hY : (matHom _ σ J g⁻¹).1 * adMat F Y = adMat F Y * C) :
    adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 = B * adMat F (cT (σ : E →+* E) Y * J) := by
  set S := sigR (AF F) σ with hS
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g).1 with hMdef
  set Mi : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g⁻¹).1 with hMidef
  have hinv : matHom (AF F) σ J g⁻¹ = (matHom (AF F) σ J g)⁻¹ := map_inv _ g
  have hMMi : M * Mi = 1 := by
    rw [hMdef, hMidef, hinv]; exact Units.mul_inv _
  have hU : cT S M * adMat F J * M = adMat F J := g.2
  have hadY : adMat F (cT (σ : E →+* E) Y * J) = cT S (adMat F Y) * adMat F J := by
    rw [adMat, Matrix.map_mul]
    congr 1
  have hJM : adMat F J * M = cT S Mi * adMat F J := by
    calc adMat F J * M = (cT S Mi * cT S M) * adMat F J * M := by
          rw [← Formalism.UG.cT_mul, hMMi, Formalism.UG.cT_one, Matrix.one_mul]
      _ = cT S Mi * (cT S M * adMat F J * M) := by simp only [Matrix.mul_assoc]
      _ = cT S Mi * adMat F J := by rw [hU]
  have h1 : adMat F (cT (σ : E →+* E) Y * J) * M = cT S C * adMat F (cT (σ : E →+* E) Y * J) := by
    rw [hadY, Matrix.mul_assoc, hJM, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hY, Formalism.UG.cT_mul, Matrix.mul_assoc]
  have hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, GlobalTheory.StdPar.yx hCM hJ hW]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : cT S C = B := by
    calc cT S C = cT S C * (adMat F (cT (σ : E →+* E) Y * J) * adMat F X) := by rw [hyx, Matrix.mul_one]
      _ = adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X := by rw [h1, Matrix.mul_assoc]
      _ = B := by rw [Matrix.mul_assoc, hX, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
  rw [h1, h2]

theorem const_centre {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {c : (AF F ⊗[F] E)ˣ} {a : GAd σ J} (ha : IsIdTorusElt σ J X Y (fun _ => c) a) :
    a ∈ levi σ J X Y {Fin.last r} ∧ ∀ m ∈ levi σ J X Y {Fin.last r}, a * m = m * a := by
  have ext : ∀ {m : GAd σ J}, m ∈ levi σ J X Y {Fin.last r} →
      (∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J m).1 * adMat F X = adMat F X * B) ∧
      ∃ C : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J m).1 * adMat F Y = adMat F Y * C := by
    intro m hm
    simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf] at hm
    obtain ⟨⟨B, -, hB⟩, ⟨C, -, hC⟩⟩ := hm (Fin.last r) (Finset.mem_singleton_self _)
    exact ⟨⟨B.1, hB⟩, ⟨C.1, hC⟩⟩
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf]
    intro k hk
    refine ⟨⟨⟨diagonal fun i => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => (((c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩,
      ⟨⟨diagonal fun i => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => ((conjUnit σ c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩⟩
    · ext i j
      have := congrFun (congrFun ha.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
    · ext i j
      have := congrFun (congrFun ha.2.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
  · obtain ⟨⟨B, hB⟩, ⟨C, hC⟩⟩ := ext hm
    obtain ⟨⟨B', hB'⟩, ⟨C', hC'⟩⟩ := ext (inv_mem hm)
    have rY := row_of_stab hCM hJ hW hB hC'
    have rX := row_of_stab hCM hJ (GlobalTheory.IdTorusCent.swap hCM hJ hW) hC hB'
    have dc : ∀ (d : AF F ⊗[F] E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)),
        diagonal (fun _ : Fin (r + 1) => d) * Z = Z * diagonal (fun _ => d) := fun d Z => by
      ext i j; simp [diagonal_mul, mul_diagonal, mul_comm]
    have c1 : (matHom _ σ J m).1 * (adMat F X * diagonal (fun _ : Fin (r + 1) => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) Y * J)) = adMat F X * diagonal (fun _ : Fin (r + 1) => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J m).1 := by
      rw [Matrix.mul_assoc (adMat F X * _), rY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB,
        Matrix.mul_assoc (adMat F X) B, ← dc, ← Matrix.mul_assoc]
    have c2 : (matHom _ σ J m).1 * (adMat F Y * diagonal (fun _ : Fin (r + 1) => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) X * J)) = adMat F Y * diagonal (fun _ : Fin (r + 1) => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) X * J) * (matHom _ σ J m).1 := by
      rw [Matrix.mul_assoc (adMat F Y * _), rX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hC,
        Matrix.mul_assoc (adMat F Y) C, ← dc, ← Matrix.mul_assoc]
    apply matHom_injective
    apply Units.ext
    simp only [map_mul, Units.val_mul, GlobalTheory.T.idelicFrameTorusElement_matrix_eq hCM hJ hW ha, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, c1, c2]

end GlobalTheory.ResidueFlow


open GlobalTheory.IdTorus in
theorem GlobalTheory.ResidueEisenstein.exists_isFlowJ : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ b : ℝ → GAd σ J, IsFlowJ σ J X Y b := by
  intro F E _ _ _ _ _ σ n J r X Y hc hJ hW
  obtain ⟨t, htc, ht⟩ := exists_continuous_isIdTorusElt hc hJ hW
  obtain ⟨l, lc, ladd, -, labs⟩ := exists_real_idele_flow F E σ hc
  have hd : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have cl := fun s : ℝ => GlobalTheory.ResidueFlow.const_centre hc hJ hW (ht fun _ => l (s / ((r + 1 : ℕ) : ℝ)))
  refine ⟨fun s => t fun _ => l (s / ((r + 1 : ℕ) : ℝ)),
    htc.comp (continuous_pi fun _ => lc.comp (continuous_id.div_const _)), fun s s' => ?_, fun s => ?_,
    fun s => (cl s).1, fun s => (cl s).2⟩
  · refine isIdTorusElt_uniq hc hJ hW (ht _) ?_
    have : (fun _ : Fin (r + 1) => l ((s + s') / ((r + 1 : ℕ) : ℝ))) =
        (fun _ => l (s / ((r + 1 : ℕ) : ℝ))) * fun _ => l (s' / ((r + 1 : ℕ) : ℝ)) := by
      funext k; rw [add_div, ladd]; rfl
    rw [this]; exact isIdTorusElt_mul (ht _) (ht _)
  · refine ⟨Units.map (Matrix.scalar (Fin (r + 1))).toMonoidHom (l (s / ((r + 1 : ℕ) : ℝ))), (ht _).1, ?_⟩
    have : Matrix.GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin (r + 1))).toMonoidHom (l (s / ((r + 1 : ℕ) : ℝ)))) =
        l (s / ((r + 1 : ℕ) : ℝ)) ^ (r + 1) := by
      apply Units.ext
      change Matrix.det (Matrix.diagonal fun _ : Fin (r + 1) => (l (s / ((r + 1 : ℕ) : ℝ))).1) = _
      rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val]
    rw [this, map_pow, NNReal.coe_pow, labs, ← Real.exp_nat_mul, mul_div_cancel₀ _ hd]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviCentreFlowWittFrameStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.exists_leviCentreFlow_wittFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ b : ℝ → GAd σ J, IsFlowJ σ J X Y b := by
  first | exact @GlobalTheory.ResidueEisenstein.exists_isFlowJ | exact GlobalTheory.ResidueEisenstein.exists_isFlowJ | (intros; apply GlobalTheory.ResidueEisenstein.exists_isFlowJ <;> assumption)
end
end
