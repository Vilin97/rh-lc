module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridCoreNodeUnitReadingIntegralCongruentStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPointMemSumTranslateOfAnnihilatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOSmulHalf

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetEquationMulRightCongruentOneModDepthIdealAl

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section
namespace GlobalTheory.CosDualStep

variable {D : D7}

theorem actO_one_left (S T : HSp D) (h : GA D T) (Z : WO S T) :
    actO S T 1 h Z = HMul.hMul (Formalism.L2.Theta.mt T h) (Z : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
  unfold actO
  simp [Formalism.L2.Theta.mt]

theorem infPart_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) : infPart D e = 0 := by
  classical
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  subst hsum
  induction P using Finset.induction_on with
  | empty => rw [Finset.sum_empty, RingHom.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem (hes a (Finset.mem_insert_self a s)).1,
      ih fun PP hPP => hes PP (Finset.mem_insert_of_mem hPP), add_zero]

def finLift {m n : ℕ} (c : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  Matrix.of fun a b => pairA D.host.F 0 1 ⊗ₜ[D.host.F] c a b

theorem smul_map_incA {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {m n : ℕ}
    (c : Matrix (Fin m) (Fin n) D.host.E) :
    e • c.map (incA D) = e • finLift c := by
  ext a b
  simp only [finLift, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [map_mul, map_mul, infPart_idemSum he, zero_mul, zero_mul]
  · rw [map_mul, map_mul, GlobalTheory.LatVac.finPart_pair, GlobalTheory.LatVac.finPart_incA]

theorem homLat_mul {a b c : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin c → D.host.E)}
    {x : Matrix (Fin c) (Fin b) D.host.E} {y : Matrix (Fin b) (Fin a) D.host.E}
    (hx : x ∈ homLat Λ' Λ'') (hy : y ∈ homLat Λ Λ') : x * y ∈ homLat Λ Λ'' := by
  show ∀ v ∈ Λ, (x * y) *ᵥ v ∈ Λ''
  intro v hv
  rw [← Matrix.mulVec_mulVec]
  exact hx _ (hy v hv)

theorem smul_homLat_mul {a b c : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} {Λ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin c → D.host.E)}
    {x : Matrix (Fin c) (Fin b) D.host.E} {y : Matrix (Fin b) (Fin a) D.host.E}
    (hx : x ∈ 𝔪 • homLat Λ' Λ'') (hy : y ∈ homLat Λ Λ') : x * y ∈ 𝔪 • homLat Λ Λ'' := by
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun p q hp hq => ?_)
  · rw [Matrix.smul_mul]
    exact Submodule.smul_mem_smul hr (homLat_mul hn hy)
  · rw [Matrix.add_mul]
    exact Submodule.add_mem _ hp hq

theorem hatMx_mul {a b c : ℕ} {M : Submodule (𝓞 D.host.E) (Matrix (Fin c) (Fin b) D.host.E)}
    {N : Submodule (𝓞 D.host.E) (Matrix (Fin c) (Fin a) D.host.E)} (y : Matrix (Fin b) (Fin a) D.host.E)
    (hMN : ∀ x ∈ M, x * y ∈ N) {u : Mx D c b} (hu : u ∈ hatMx M) : u * y.map (incA D) ∈ hatMx N := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, x * y, hMN x hx, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show _ * (Algebra.TensorProduct.includeRight (y k j)) = _
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add p q _ _ hp hq => rw [Matrix.add_mul]; exact add_mem hp hq
  | neg p _ hp => rw [Matrix.neg_mul]; exact neg_mem hp

theorem smul_one_sub {n : ℕ} (e : AE D) (A A' C : Matrix (Fin n) (Fin n) (AE D)) (h : e • A = e • C) :
    e • (1 - (A' - C)) = e • (1 + A - A') := by
  rw [smul_sub, smul_sub, smul_sub, smul_add, h]
  abel

theorem core_step {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {n n' : ℕ}
    (x₀ : Matrix (Fin n) (Fin n') D.host.E) (y₀ : Matrix (Fin n') (Fin n) D.host.E)
    (mg : Matrix (Fin n) (Fin n) (AE D)) (u u' : Matrix (Fin n) (Fin n') (AE D))
    (heq : e • (x₀.map (incA D) - u) = HMul.hMul mg (e • (x₀.map (incA D) - u'))) :
    e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul u (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1))) =
      HMul.hMul mg (e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul u' (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1)))) := by
  have hxy : x₀ * y₀ = 1 + (x₀ * y₀ - 1) := by abel
  have hXY : HMul.hMul (x₀.map (incA D)) (y₀.map (incA D)) = (1 : Matrix (Fin n) (Fin n) (AE D)) + (x₀ * y₀ - 1).map (incA D) := by
    rw [← Matrix.map_mul]
    conv_lhs => rw [hxy]
    rw [Matrix.map_add (incA D) (fun a b => RingHom.map_add _ a b),
      Matrix.map_one (incA D) (RingHom.map_zero _) (RingHom.map_one _)]
  have hce := smul_map_incA he (x₀ * y₀ - 1)
  have key : ∀ v : Matrix (Fin n) (Fin n') (AE D),
      e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul v (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1))) =
        HMul.hMul (e • (x₀.map (incA D) - v)) (y₀.map (incA D)) := by
    intro v
    rw [Matrix.smul_mul, Matrix.sub_mul, hXY]
    exact smul_one_sub e _ _ _ hce
  rw [key u, key u', heq, Matrix.mul_assoc]

theorem coset_equation_mul_right_congruent_one_mod_depthIdeal : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ u ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), ∀ u' ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))),
    e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u) =
      actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u')) →
    ∃ a₁ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))), ∃ a₂ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))),
      e • ((1 : WO (G.V (.core i)) (G.V (.core i))) - a₁) = actO (G.V (.core i)) (G.V (.core i)) 1 g (e • (1 - a₂)) := by
  intro D _ T L μ0 _ sc G W M _ i _ x₀ hx₀ e he g u hu u' hu' heq
  obtain ⟨-, y₀, hy₀, hc⟩ := hx₀
  have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by simp
  have hcf : finLift (x₀ * y₀ - 1) ∈
      hatMx (G.modul • homLat (G.Λ (.core i)) (G.Λ (.core i))) :=
    AddSubgroup.subset_closure ⟨1, h1, x₀ * y₀ - 1, hc, rfl⟩
  have hmul : ∀ x ∈ G.modul • homLat (G.latS (.core i)) (G.latT (.core i)),
      x * y₀ ∈ G.modul • homLat (G.Λ (.core i)) (G.Λ (.core i)) := fun x hx => smul_homLat_mul hx hy₀
  refine ⟨_, sub_mem (hatMx_mul y₀ hmul hu) hcf, _, sub_mem (hatMx_mul y₀ hmul hu') hcf, ?_⟩
  rw [actO_one_left] at heq ⊢
  exact core_step he x₀ y₀ _ u u' heq

end GlobalTheory.CosDualStep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetEquationMulRightCongruentOneModDepthIdealAlStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix


theorem _root_.GlobalTheory.T.coset_equation_mul_right_congruent_one_mod_depthIdeal_alt : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ u ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), ∀ u' ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))),
    e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u) =
      actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u')) →
    ∃ a₁ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))), ∃ a₂ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))),
      e • ((1 : WO (G.V (.core i)) (G.V (.core i))) - a₁) = actO (G.V (.core i)) (G.V (.core i)) 1 g (e • (1 - a₂)) := by
  first | exact @GlobalTheory.CosDualStep.coset_equation_mul_right_congruent_one_mod_depthIdeal | exact GlobalTheory.CosDualStep.coset_equation_mul_right_congruent_one_mod_depthIdeal | (intros; apply GlobalTheory.CosDualStep.coset_equation_mul_right_congruent_one_mod_depthIdeal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetCharConditionIntegralUnitCongruentDepth

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section
namespace GlobalTheory.CosDual

theorem ann_depLat : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
    (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
    ∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1 := by
  intro D hq T L μ0 hL sc G W M hM i hi e he y hy h u hu
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have h1 := h (e • u) (hu.2 e he)
  rw [smul_smul, hee, symplO_smul_half _ _ e u y hy] at h1
  exact h1



theorem cosDual : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)),
    (∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u (actO _ _ 1 g⁻¹ y)) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) =
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) (actO _ _ 1 g⁻¹ y))) →
    ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)),
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • (((Lev.finE (G.V (.core i)) g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.core i)) := by
  intro D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g hyp x hx
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨X, hXdef⟩ : ∃ X : WO (G.pS (.core i)) (G.pT (.core i)), X = e • x₀.map (incA D) := ⟨_, rfl⟩
  have hXh : IsHalf e X := fun a b => by
    simp only [hXdef, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  obtain ⟨Z, hZdef⟩ : ∃ Z : WO (G.pS (.core i)) (G.pT (.core i)), Z = X - actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := ⟨_, rfl⟩
  have hZ : IsHalf e Z := fun a b => by
    simp only [hZdef, Matrix.sub_apply, mul_sub, hXh a b, half_actO _ _ e g X hXh a b]
  have key : ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO _ _ 1 g (e • v)) y) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) = 1 := by
    intro y hy h1 h2
    have hy' : IsHalf (cA D e) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g⁻¹ y) := half_actO _ _ _ _ _ hy
    have hA := ann_depLat D hq T L μ0 hL sc G W M hM i hi e he y hy h1
    have hB := ann_depLat D hq T L μ0 hL sc G W M hM i hi e he _ hy' (fun v hv => by
      have h3 := h2 v hv
      rw [← GlobalTheory.SymplOInv.symplO_actO D _ _ 1 g (e • v) (actO _ _ 1 g⁻¹ y), actO_inv]
      exact h3)
    have H := hyp y hy hA hB
    rw [← hXdef] at H
    rw [← GlobalTheory.SymplOInv.symplO_actO D _ _ 1 g X (actO _ _ 1 g⁻¹ y), actO_inv] at H
    have hsum : X = Z + actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := by
      rw [hZdef]; abel
    have hs : symplO (G.pS (.core i)) (G.pT (.core i)) X y =
        symplO (G.pS (.core i)) (G.pT (.core i)) Z y +
          symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y := by
      conv_lhs => rw [hsum]
      exact GlobalTheory.LatVac.symplO_add_left _ _ _ _ _
    rw [hs, AddChar.map_add_eq_mul] at H
    generalize hcdef : W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) = c at H
    have hc : c ≠ 0 := by
      intro h0
      have h5 : W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) *
          W.ψ (-(symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y)) = 1 := by
        rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
      rw [show W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) = c from hcdef,
        h0, zero_mul] at h5
      exact zero_ne_one h5
    have H' : (W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) - 1) * c = 0 := by
      rw [sub_mul, H, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 H').resolve_right hc)
  obtain ⟨a, ha, b, hb, hZeq⟩ := GlobalTheory.T.halfPoint_mem_sum_translate_of_annihilator D hq T L μ0 hL sc G W M hM i hi e he g Z hZ key
  have heq : e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - a) =
      actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - -b)) := by
    rw [smul_sub, sub_neg_eq_add, smul_add, actO_add, ← hXdef]
    have h6 : X = Z + actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := by rw [hZdef]; abel
    rw [hZeq] at h6
    conv_lhs => rw [h6]
    abel
  obtain ⟨a₁, h1, a₂, h2, heq2⟩ := GlobalTheory.T.coset_equation_mul_right_congruent_one_mod_depthIdeal_alt D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g a ha (-b) (neg_mem hb) heq
  exact GlobalTheory.T.gridCoreNode_unitReading_integral_congruent D hq T L μ0 hL sc G W M hM i hi e he g a₁ h1 a₂ h2 heq2 x hx

end GlobalTheory.CosDual
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetCharConditionIntegralUnitCongruentDepthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix


theorem _root_.GlobalTheory.T.cosetCharCondition_integral_unit_congruent_depth : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)),
    (∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u (actO _ _ 1 g⁻¹ y)) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) =
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) (actO _ _ 1 g⁻¹ y))) →
    ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)),
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • (((Lev.finE (G.V (.core i)) g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.core i)) := by
  first | exact @GlobalTheory.CosDual.cosDual | exact GlobalTheory.CosDual.cosDual | (intros; apply GlobalTheory.CosDual.cosDual <;> assumption)
end
end
