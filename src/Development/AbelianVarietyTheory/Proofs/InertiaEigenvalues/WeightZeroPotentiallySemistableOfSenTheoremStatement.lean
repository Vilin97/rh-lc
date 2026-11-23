module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFilZeroSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteInertiaImpliesPotSemistableProofStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenAdmissibleRepresentationFiniteInertiaStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedExtFixedFieldFrobeniusPowDegreeStatement
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRestrictionUnramifiedFrobeniusConjugates

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem RestrScalars.fr_smul (l : ℕ) [Fact l.Prime] (m : ℕ) (a : ℚ_[l]) (x : ↥(MaximalUnramifiedExtension l)) : fr l m (a • x) = a • fr l m x := by
  show (frobUr l ^ m) (a • x) = a • (frobUr l ^ m) x
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]

theorem RestrScalars.fr_comm_pow (l : ℕ) [Fact l.Prime] (a b : ℕ) (x : ↥(MaximalUnramifiedExtension l)) : fr l a (fr l b x) = fr l b (fr l a x) := by
  show (frobUr l ^ a) ((frobUr l ^ b) x) = (frobUr l ^ b) ((frobUr l ^ a) x)
  rw [← AlgHom.mul_apply, ← AlgHom.mul_apply, ← pow_add, ← pow_add, add_comm]

theorem weilRes_of_basis (hE : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (E : FinExt l) (ω : Fin r → ↥(MaximalUnramifiedExtension l)),
      E.1 ≤ MaximalUnramifiedExtension l ∧ Module.finrank ℚ_[l] ↥E.1 = r ∧ (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c ↔ (c : Om l) ∈ E.1) ∧
      (∀ k, fr l r (ω k) = ω k) ∧ LinearIndependent ℚ_[l] ω ∧
      (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) ∧
      (Matrix.of fun m k : Fin r => fr l m (ω k)).det ≠ 0) : WeilRes := by
  intro l _ n _ _ K r ρ hρ
  obtain ⟨E, ω, -, -, -, hωf, hli, hsp, hdet⟩ := hE l r hρ.pos

  set v : Fin r → Om l := fun k => ((ω k : ↥(MaximalUnramifiedExtension l)) : Om l) with hvdef
  have hv : LinearIndependent ℚ_[l] v := by
    have := hli.map' ((MaximalUnramifiedExtension l).val.toLinearMap) (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    exact this
  set S : Submodule ℚ_[l] (Om l) := Submodule.span ℚ_[l] (Set.range v)
  let bS : Module.Basis (Fin r) ℚ_[l] S := Module.Basis.span hv
  haveI : FiniteDimensional ℚ_[l] S := Module.Finite.of_basis bS
  have coe_sum : ∀ a : Fin r → ℚ_[l], (((∑ k, a k • ω k : ↥(MaximalUnramifiedExtension l))) : Om l) = ∑ k, a k • v k := by
    intro a
    simp [hvdef]
  have memS : ∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → (c : Om l) ∈ S := by
    intro c hc
    obtain ⟨a, rfl⟩ := hsp c hc
    rw [coe_sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have fix : ∀ g i j k, fr l r ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k) = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k := by
    intro g i j k
    rw [map_mul, hρ.rat, hωf]

  let co : ↥(GK K) → n → n → Fin r → Fin r → ℚ_[l] := fun g i j k k' =>
    bS.repr ⟨_, memS _ (fix g i j k)⟩ k'
  have hco : ∀ g i j k, ∑ k', co g i j k k' • ω k' = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k := by
    intro g i j k
    apply Subtype.val_injective
    rw [coe_sum]
    have h := bS.sum_repr ⟨_, memS _ (fix g i j k)⟩
    have h2 := congrArg Subtype.val h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Module.Basis.span_apply]
  let M : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ℚ_[l] := fun g =>
    Matrix.of fun x y => co g x.1 y.1 y.2 x.2

  let W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l) := Matrix.of fun m k : Fin r => fr l m (ω k)
  let pm : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := Matrix.kroneckerMap (· * ·) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) W
  have hpdet : pm.det ≠ 0 := by
    have : pm.det = W.det ^ Fintype.card n := by
      exact (Matrix.det_kronecker (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) W).trans (by simp)
    rw [this]
    exact pow_ne_zero _ hdet
  let pU : GL (n × Fin r) ↥(MaximalUnramifiedExtension l) := ((Matrix.isUnit_iff_isUnit_det pm).mpr (isUnit_iff_ne_zero.mpr hpdet)).unit
  have hpU : (pU : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = pm := rfl
  let D : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := fun g =>
    Matrix.blockDiagonal (fun m : Fin r => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))
  have key : ∀ g, pm * (M g).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) = D g * pm := by
    intro g
    refine Matrix.ext fun x y => ?_
    obtain ⟨i, m⟩ := x
    obtain ⟨j, k⟩ := y
    simp only [pm, D, M, W, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_ite_irrel, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.blockDiagonal_apply, Matrix.map_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]

    rw [← map_mul, ← hco g i j k, map_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [RestrScalars.fr_smul, Algebra.smul_def, mul_comm]
  have key' : ∀ g, (M g).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) = ((pU⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix _ _ _) * D g * pm := by
    intro g
    rw [Matrix.mul_assoc, ← key g, ← Matrix.mul_assoc, ← hpU, Units.inv_mul, Matrix.one_mul]
  have hinj : Function.Injective (fun X : Matrix (n × Fin r) (n × Fin r) ℚ_[l] => X.map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))) :=
    Matrix.map_injective (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)).injective
  have Dmul : ∀ g h, D (g * h) = D g * D h := by
    intro g h
    simp only [D]
    rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext m
    rw [map_mul, Units.val_mul]
    exact Matrix.map_mul
  have D1 : D 1 = 1 := by
    simp only [D, map_one, Units.val_one]
    rw [← Matrix.blockDiagonal_one]
    congr 1
    funext m
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let f : ↥(GK K) →* Matrix (n × Fin r) (n × Fin r) ℚ_[l] :=
    { toFun := M
      map_one' := by
        apply hinj
        simp only
        rw [key', D1, Matrix.mul_one, ← hpU, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      map_mul' := by
        intro g h
        apply hinj
        simp only
        rw [Matrix.map_mul, key', key', key', Dmul]
        have : pm * ((pU⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix _ _ _) = 1 := by rw [← hpU, Units.mul_inv]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc pm, this, Matrix.one_mul] }
  refine ⟨f.toHomUnits, pU, ?_, ?_, ?_⟩
  · intro x y
    have hc : Continuous fun g : ↥(GK K) => bS.coord x.2 ⟨_, memS _ (fix g x.1 y.1 y.2)⟩ := by
      refine (LinearMap.continuous_of_finiteDimensional (bS.coord x.2)).comp ?_
      refine Continuous.subtype_mk ?_ _
      exact (hρ.cont x.1 y.1).mul continuous_const
    simpa [f, M, co] using hc
  · intro x y
    rw [hpU]
    obtain ⟨i, m⟩ := x
    obtain ⟨j, k⟩ := y
    simp only [pm, W, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    split_ifs
    · rw [RestrScalars.fr_comm_pow, hωf]
    · exact map_zero _
  · intro g
    rw [hpU]
    exact key g

theorem weilRes : WeilRes := weilRes_of_basis GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree

end GlobalTheory.PMon

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRestrictionUnramifiedFrobeniusConjugatesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.weilRestriction_unramified_frobeniusConjugates : WeilRes := by
  first | exact @GlobalTheory.PMon.weilRes | exact GlobalTheory.PMon.weilRes | (intros; apply GlobalTheory.PMon.weilRes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightZeroPotentiallySemistableOfSenTheorem

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.PMon

theorem fr_zero_apply (l : ℕ) [Fact l.Prime] (c : ↥(MaximalUnramifiedExtension l)) : fr l 0 c = c := by
  unfold fr
  rw [pow_zero]
  rfl

theorem senStep : SenStep := by
  intro l _ P AI T n _ _ K r ρ hρ hF
  classical
  obtain ⟨ρ₀, p, hc₀, hp, hρ₀⟩ := GlobalTheory.T.weilRestriction_unramified_frobeniusConjugates l n K r ρ hρ
  obtain ⟨S, θ, hS, -, -, hθΩ, hθg⟩ := GlobalTheory.T.exists_theta_deRhamFilZero_surjective l P AI T
  choose U hU hUg using hF
  have hΩ : ∀ y : Om l, algebraMap (Om l) P.R.BdR y ∈ S := fun y => (hθΩ y).1
  have hkd : ∀ c : ↥(MaximalUnramifiedExtension l), kd P c ∈ S := fun c => hΩ _
  let kS : ↥(MaximalUnramifiedExtension l) →+* ↥S := (kd P).codRestrict S hkd
  let Φ := (kd P).mapMatrix (m := n × Fin r)
  let ΦS := kS.mapMatrix (m := n × Fin r)
  let ιS := S.subtype.mapMatrix (m := n × Fin r)
  have hinj : Function.Injective ιS := Matrix.map_injective Subtype.val_injective
  have hιΦ : ∀ A, ιS (ΦS A) = Φ A := fun A => by ext i j; rfl
  have hpp : Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hpp' : Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]

  have hfix : ∀ g : ↥(GK K), (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (Φ p) = Φ p := by
    intro g
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Φ]
    have hK : ((((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)) ∈ K.1 := hρ.le _ (hp i j)
    have hg := (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ hK
    show P.actQdR (g : GQ l) (algebraMap (Om l) P.R.BdR _) = algebraMap (Om l) P.R.BdR _
    rw [P.actQdR_Om]
    exact congrArg _ hg

  let Ut : Matrix (n × Fin r) (n × Fin r) P.R.BdR := Matrix.blockDiagonal fun m => (U m : Matrix n n P.R.BdR)
  let Ut' : Matrix (n × Fin r) (n × Fin r) P.R.BdR := Matrix.blockDiagonal fun m => ((U m)⁻¹ : GL n P.R.BdR)
  have hUU : Ut * Ut' = 1 := by
    simp only [Ut, Ut']
    rw [← Matrix.blockDiagonal_mul]
    have : (fun m => (U m : Matrix n n P.R.BdR) * ((U m)⁻¹ : GL n P.R.BdR)) = fun _ => 1 := by
      funext m; exact Units.mul_inv (U m)
    rw [this]
    exact Matrix.blockDiagonal_one
  let US : Fin r → Matrix n n ↥S := fun m => Matrix.of fun i j => ⟨(U m : Matrix n n P.R.BdR) i j, (hS _).2 ((hU m).1 i j)⟩
  let VS : Fin r → Matrix n n ↥S := fun m => Matrix.of fun i j =>
    ⟨((U m)⁻¹ : GL n P.R.BdR) i j, (hS _).2 ((hU m).2 i j)⟩
  let XS := ΦS ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Matrix.blockDiagonal US
  let YS := Matrix.blockDiagonal VS * ΦS (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))
  have hX : ιS XS = Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Ut := by
    simp only [XS, map_mul, hιΦ]
    congr 1
    simp only [ιS, RingHom.mapMatrix_apply, Ut]
    rw [Matrix.blockDiagonal_map _ _ (by simp)]
    rfl
  have hY : ιS YS = Ut' * Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) := by
    simp only [YS, map_mul, hιΦ]
    congr 1
    simp only [ιS, RingHom.mapMatrix_apply, Ut']
    rw [Matrix.blockDiagonal_map _ _ (by simp)]
    rfl
  have hXY : XS * YS = 1 := by
    apply hinj
    rw [map_mul, hX, hY, map_one, mul_assoc, ← mul_assoc Ut, hUU, one_mul, hpp']

  have hmain : ∀ g : ↥(GK K),
      Φ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))) *
        (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (ιS XS) = ιS XS := by
    intro g
    set Ψ := (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (m := n × Fin r)
    set pk := Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))
    set pki := Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))
    set R₀ := Φ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)))
    set Dk := Φ (Matrix.blockDiagonal fun m : Fin r => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))
    have hW : pk * R₀ = Dk * pk := by
      simp only [pk, R₀, Dk, ← map_mul, hρ₀ g]
    have hD : Dk * Ψ Ut = Ut := by
      have h1 : Dk = Matrix.blockDiagonal fun m : Fin r => matD P ρ m g := by
        simp only [Dk, Φ, RingHom.mapMatrix_apply]
        rw [Matrix.blockDiagonal_map _ _ (by simp)]
        rfl
      have h2 : Ψ Ut = Matrix.blockDiagonal fun m : Fin r => (U m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) := by
        simp only [Ψ, Ut, RingHom.mapMatrix_apply]
        rw [Matrix.blockDiagonal_map _ _ (by simp)]
        rfl
      rw [h1, h2, ← Matrix.blockDiagonal_mul]
      congr 1
      funext m
      rw [hUg m g]
      simp
    have hΨpki : Ψ pki = pki := by
      have hΨp : Ψ pk = pk := hfix g
      calc Ψ pki = Ψ pki * (pk * pki) := by rw [hpp, mul_one]
        _ = Ψ (pki * pk) * pki := by rw [map_mul, hΨp, mul_assoc]
        _ = pki := by rw [hpp', map_one, one_mul]
    have hR : R₀ = pki * Dk * pk := by
      calc R₀ = pki * (pk * R₀) := by rw [← mul_assoc, hpp', one_mul]
        _ = pki * Dk * pk := by rw [hW, mul_assoc]
    rw [hX, map_mul, hΨpki, hR]
    calc pki * Dk * pk * (pki * Ψ Ut) = pki * (Dk * Ψ Ut) := by
          simp only [mul_assoc]
          rw [← mul_assoc pk pki, hpp, one_mul]
      _ = pki * Ut := by rw [hD]

  let actS : GQ l → ↥S → ↥S := fun g x => ⟨P.actQdR g x, (hθg g x).1⟩
  let qS : ℚ_[l] → ↥S := fun q => kS (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q)
  have hES : ∀ g : ↥(GK K), (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map qS * XS.map (actS (g : GQ l)) = XS := by
    intro g
    apply hinj
    have e1 : ιS ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map qS) =
        Φ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))) := by ext i j; rfl
    have e2 : ιS (XS.map (actS (g : GQ l))) = (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (ιS XS) := by
      ext i j; rfl
    rw [map_mul, e1, e2]
    exact hmain g
  let Θ := θ.mapMatrix (m := n × Fin r)
  have hMM : Θ XS * Θ YS = 1 := by rw [← map_mul, hXY, map_one]
  let Mu : GL (n × Fin r) ℂ_[l] := ⟨Θ XS, Θ YS, hMM, (by first | exact mul_eq_one_comm.mp hMM | exact Matrix.mul_eq_one_comm.1 hMM)⟩
  have hSen : ∀ g : ↥(GK K), (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) *
      (Mu : Matrix (n × Fin r) (n × Fin r) ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = Mu := by
    intro g
    have h1 : (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) =
        Θ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map qS) := by
      ext i j
      simp only [Θ, RingHom.mapMatrix_apply, Matrix.map_apply]
      have := (hθΩ (((algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j)) : ↥(MaximalUnramifiedExtension l)) : Om l)).2
      exact this.symm
    have h2 : (Mu : Matrix (n × Fin r) (n × Fin r) ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = Θ (XS.map (actS (g : GQ l))) := by
      ext i j
      simp only [Θ, RingHom.mapMatrix_apply, Matrix.map_apply]
      exact ((hθg (g : GQ l) (XS i j)).2).symm
    rw [h1, h2, ← map_mul, hES g]
  have hfin₀ := GlobalTheory.T.sen_admissible_representation_finite_inertia l (n × Fin r) K ρ₀ hc₀ Mu hSen

  have hr : 0 < r := hρ.pos
  let z : Fin r := ⟨0, hr⟩
  let F : GL (n × Fin r) ℚ_[l] → Matrix n n ↥(MaximalUnramifiedExtension l) := fun A => Matrix.of fun i j =>
    ((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * (A : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) *
      ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) (i, z) (j, z)
  have hFρ : ∀ g, F (ρ₀ g) = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) := by
    intro g
    ext i j
    simp only [F, Matrix.of_apply]
    rw [hρ₀ g, mul_assoc, Units.mul_inv, mul_one, Matrix.blockDiagonal_apply_eq, Matrix.map_apply]
    exact congrArg Subtype.val (fr_zero_apply l ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j))
  have hfin : (ρ '' (IK K : Set ↥(GK K))).Finite := by
    have h1 : ((fun A : GL n ↥(MaximalUnramifiedExtension l) => (A : Matrix n n ↥(MaximalUnramifiedExtension l))) '' (ρ '' (IK K : Set ↥(GK K)))).Finite := by
      rw [Set.image_image]
      have : (fun g => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l))) '' (IK K : Set ↥(GK K)) = F '' (ρ₀ '' (IK K : Set ↥(GK K))) := by
        rw [Set.image_image]
        simp only [hFρ]
      rw [this]
      exact hfin₀.image F
    exact Set.Finite.of_finite_image h1 (fun a _ b _ h => Units.ext h)
  exact GlobalTheory.T.finiteInertiaImpliesPotSemistable_proof l P AI T n K r ρ hρ hfin

end GlobalTheory.PMon
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightZeroPotentiallySemistableOfSenTheoremStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.weightZero_potentiallySemistable_of_sen_theorem : SenStep := by
  first | exact @GlobalTheory.PMon.senStep | exact GlobalTheory.PMon.senStep | (intros; apply GlobalTheory.PMon.senStep <;> assumption)
end
end
