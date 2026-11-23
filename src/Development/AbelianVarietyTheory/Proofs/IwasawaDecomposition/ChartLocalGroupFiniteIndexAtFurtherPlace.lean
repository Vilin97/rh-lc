module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupContainsPrincipalCongruence
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupLeBaseLatticeLevel
public import Formalism.SatakeDualWeyl.StatementC
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupContainsPrincipalCongruenceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chart_local_group_contains_principal_congruence : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom := by
  first | exact @GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ | exact GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ | (intros; apply GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupLeBaseLatticeLevelStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chart_localGroup_le_baseLattice_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0 := by
  first | exact @GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base | exact GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base | (intros; apply GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base <;> assumption)
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.Development

section

@[expose] public section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.LPI

open Formalism.UG

def PLGen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (O : Subring R) (n k : ℕ)
    (Lb : Submodule (𝓞 E) (Fin n → E)) (m : Fin k → Fin n → E),
    (∀ i, m i ∈ Lb) → (∀ l ∈ Lb, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) →
    ∀ y : Fin n → E ⊗[F] R,
      y ∈ latS (F := F) R (tensInt (F := F) R (intOE E) O) Lb ↔
        ∃ a : Fin k → R, (∀ i, a i ∈ O) ∧ y = fun j => ∑ i, m i j ⊗ₜ[F] a i

end PI.LPI
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.ZeroMemLatSet

section

@[expose] public section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.LevelProdIdx

open Formalism.UG

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ}

def latSet (R : Type) [CommRing R] [Algebra F R] (O : Subring R) {k : ℕ} (G : Fin k → (Fin n → E)) :
    Set (Fin n → E ⊗[F] R) :=
  {y | ∃ c : Fin k → R, (∀ i, c i ∈ O) ∧ y = fun l => ∑ i, G i l ⊗ₜ[F] c i}

section Set

variable {R : Type} [CommRing R] [Algebra F R] {O : Subring R} {k : ℕ} {G : Fin k → (Fin n → E)}

theorem zero_mem_latSet : (0 : Fin n → E ⊗[F] R) ∈ latSet R O G := ⟨0, fun _ => O.zero_mem, by funext l; simp⟩

theorem add_mem_latSet {y z : Fin n → E ⊗[F] R} (hy : y ∈ latSet R O G) (hz : z ∈ latSet R O G) :
    y + z ∈ latSet R O G := by
  obtain ⟨c, hc, rfl⟩ := hy
  obtain ⟨c', hc', rfl⟩ := hz
  refine ⟨c + c', fun i => O.add_mem (hc i) (hc' i), ?_⟩
  funext l
  simp [TensorProduct.tmul_add, Finset.sum_add_distrib]

theorem neg_mem_latSet {y : Fin n → E ⊗[F] R} (hy : y ∈ latSet R O G) :
    -y ∈ latSet R O G := by
  obtain ⟨c, hc, rfl⟩ := hy
  refine ⟨-c, fun i => O.neg_mem (hc i), ?_⟩
  funext l
  simp [TensorProduct.tmul_neg, Finset.sum_neg_distrib]

theorem smul_mem_latSet [NumberField E]
    (hG : ∀ i (o : 𝓞 E), ∃ z : Fin k → ℤ, ∀ l, (o : E) * G i l = ∑ j, z j • G j l)
    {s : E ⊗[F] R} (hs : s ∈ tensInt (F := F) R (intOE E) O) :
    ∀ y : Fin n → E ⊗[F] R, y ∈ latSet R O G → s • y ∈ latSet R O G := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rintro y ⟨c, hc, rfl⟩
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨d, hd⟩, rfl⟩
    · obtain ⟨o, rfl⟩ := he
      choose z hz using fun i => hG i o
      refine ⟨fun j => ∑ i, z i j • c i, fun j => sum_mem fun i _ => zsmul_mem (hc i) _, ?_⟩
      ext l
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, hz, TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
      exact Finset.sum_comm
    · refine ⟨fun i => d * c i, fun i => mul_mem hd (hc i), ?_⟩
      ext l
      simp [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
  | zero => intro y _; rw [zero_smul]; exact zero_mem_latSet
  | one => intro y hy; rwa [one_smul]
  | add a b _ _ ha hb => intro y hy; rw [add_smul]; exact add_mem_latSet (ha y hy) (hb y hy)
  | neg a _ ha => intro y hy; rw [neg_smul]; exact neg_mem_latSet (ha y hy)
  | mul a b _ _ ha hb => intro y hy; rw [mul_smul]; exact ha _ (hb y hy)

end Set

variable [NumberField E]

theorem mem_latS_iff (R : Type) [CommRing R] [Algebra F R] (O : Subring R)
    (Λ : Submodule (𝓞 E) (Fin n → E)) {k : ℕ} (G : Fin k → (Fin n → E)) (hGm : ∀ i, G i ∈ Λ)
    (hΛ : ∀ x ∈ Λ, ∃ z : Fin k → ℤ, x = ∑ j, z j • G j) (y : Fin n → E ⊗[F] R) :
    y ∈ latS (F := F) R (tensInt (F := F) R (intOE E) O) Λ ↔ y ∈ latSet R O G := by
  have hG : ∀ i (o : 𝓞 E), ∃ z : Fin k → ℤ, ∀ l, (o : E) * G i l = ∑ j, z j • G j l := by
    intro i o
    obtain ⟨z, hz⟩ := hΛ _ (Λ.smul_mem o (hGm i))
    refine ⟨z, fun l => ?_⟩
    calc (o : E) * G i l = (o • G i) l := rfl
      _ = _ := by rw [hz]; simp [Finset.sum_apply]
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨z, rfl⟩ := hΛ x hx
      refine ⟨fun j => ((z j : R)), fun j => intCast_mem _ _, ?_⟩
      ext l
      simp only [inclE, Finset.sum_apply, Pi.smul_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
        TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]
    | zero => exact zero_mem_latSet
    | add a b _ _ ha hb => exact add_mem_latSet ha hb
    | smul a x _ hx => exact smul_mem_latSet hG a.2 x hx
  · rintro ⟨c, hc, rfl⟩
    have : (fun l => ∑ i, G i l ⊗ₜ[F] c i) =
        ∑ i, (⟨(1 : E) ⊗ₜ[F] c i, Subring.subset_closure (Or.inr ⟨⟨c i, hc i⟩, rfl⟩)⟩ :
          tensInt (F := F) R (intOE E) O) • (fun l => inclE (F := F) R (G i l)) := by
      ext l
      simp [Finset.sum_apply, inclE, Algebra.TensorProduct.tmul_mul_tmul, Subring.smul_def]
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨G i, hGm i, rfl⟩)

end PI.UnitaryGroupMassFormula.LevelProdIdx

namespace PI.LPI

theorem plGen : PLGen := by
  intro F E _ _ _ _ _ R _ _ O n k Lb m hm hLb y
  exact PI.UnitaryGroupMassFormula.LevelProdIdx.mem_latS_iff R O Lb m hm hLb y

end PI.LPI
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupFiniteIndexAtFurtherPlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.FinAtQ

section Abs

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S] [Algebra S R]

def mulSub (L : Submodule S (n → R)) (g : ℕ) : AddSubgroup L where
  carrier := {y | ∃ z : L, (y : n → R) = g • (z : n → R)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨z, hz⟩ ⟨w, hw⟩
    exact ⟨z + w, by simp [hz, hw, smul_add]⟩
  neg_mem' := by
    rintro a ⟨z, hz⟩
    exact ⟨-z, by simp [hz]⟩

def actL (L : Submodule S (n → R)) (x : GL n R) (hx : x ∈ stabGL L) : L →+ L where
  toFun y := ⟨(x : Matrix n n R) *ᵥ (y : n → R), (hx y).1 y.2⟩
  map_zero' := by ext1; simp
  map_add' a b := by ext1; simp [Matrix.mulVec_add]

theorem mulSub_le_comap (L : Submodule S (n → R)) (g : ℕ) (x : GL n R) (hx : x ∈ stabGL L) :
    mulSub L g ≤ (mulSub L g).comap (actL L x hx) := by
  rintro y ⟨z, hz⟩
  refine ⟨actL L x hx z, ?_⟩
  simp only [actL, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [hz, Matrix.mulVec_smul]

def actQ (L : Submodule S (n → R)) (g : ℕ) (x : GL n R) (hx : x ∈ stabGL L) :
    (L ⧸ mulSub L g) →+ (L ⧸ mulSub L g) :=
  QuotientAddGroup.map _ _ (actL L x hx) (mulSub_le_comap L g x hx)

theorem actQ_mk (L : Submodule S (n → R)) (g : ℕ) (x : GL n R) (hx : x ∈ stabGL L) (y : L) :
    actQ L g x hx (y : L ⧸ mulSub L g) = ((actL L x hx y : L) : L ⧸ mulSub L g) := rfl

def rho (L : Submodule S (n → R)) (g : ℕ) (W : Subgroup (GL n R)) (hW : W ≤ stabGL L) :
    W →* AddMonoid.End (L ⧸ mulSub L g) where
  toFun x := actQ L g x (hW x.2)
  map_one' := by
    show actQ L g 1 _ = AddMonoidHom.id _
    refine AddMonoidHom.ext fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      rw [actQ_mk]
      congr 1
      ext1
      simp [actL]
  map_mul' a b := by
    show actQ L g (a * b : W) _ = (actQ L g a (hW a.2)).comp (actQ L g b (hW b.2))
    refine AddMonoidHom.ext fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      rw [AddMonoidHom.comp_apply, actQ_mk, actQ_mk, actQ_mk]
      congr 1
      ext1
      simp [actL, Matrix.mulVec_mulVec]

theorem finiteIndex_of_trivOn (L : Submodule S (n → R)) (g : ℕ) (hQ : Finite (L ⧸ mulSub L g))
    (H W : Subgroup (GL n R)) (hW : W ≤ stabGL L)
    (hH : ∀ x ∈ W, (∀ y ∈ L, ∃ z ∈ L, (x : Matrix n n R) *ᵥ y - y = g • z) → x ∈ H) :
    (H.subgroupOf W).FiniteIndex := by
  have hE : Finite (AddMonoid.End (L ⧸ mulSub L g)) :=
    Finite.of_injective (fun f : AddMonoid.End (L ⧸ mulSub L g) => (f : (L ⧸ mulSub L g) → (L ⧸ mulSub L g)))
      (fun a b h => AddMonoidHom.ext (congrFun h))
  have hU : Finite (AddMonoid.End (L ⧸ mulSub L g))ˣ := Finite.of_injective _ Units.val_injective
  have h1 : (rho L g W hW).toHomUnits.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  refine Subgroup.finiteIndex_of_le (H := (rho L g W hW).toHomUnits.ker) ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : rho L g W hW x = 1 := congrArg Units.val hx
  rw [Subgroup.mem_subgroupOf]
  refine hH x x.2 fun y hy => ?_
  have h2 : actQ L g x (hW x.2) ((⟨y, hy⟩ : L) : L ⧸ mulSub L g) = ((⟨y, hy⟩ : L) : L ⧸ mulSub L g) :=
    DFunLike.congr_fun hx' _
  rw [actQ_mk, QuotientAddGroup.eq] at h2
  obtain ⟨z, hz⟩ := h2
  refine ⟨-(z : n → R), (-z).2, ?_⟩
  have hz' : -(((x : GL n R) : Matrix n n R) *ᵥ y) + y = g • (z : n → R) := by
    simpa [actL] using hz
  rw [smul_neg, ← hz', neg_add, neg_neg, sub_eq_add_neg, add_comm]

end Abs

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finite_quot (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Module.Finite (𝓞 E) Λ) (g : ℕ) (hg : g ≠ 0) :
    Finite (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ ⧸
      mulSub (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ) g) := by
  set L := latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ with hL
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  let m : Fin k → Fin n → E := fun i => (s i : Fin n → E)
  have hm : ∀ i, m i ∈ Λ := fun i => (s i).2
  have hgen : ∀ l ∈ Λ, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i := by
    intro l hl
    have h0 : (⟨l, hl⟩ : Λ) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h0
    refine ⟨c, ?_⟩
    have h1 := congrArg Subtype.val hc
    rw [Submodule.coe_sum] at h1
    simpa [m] using h1.symm
  have key := fun y => PI.LPI.plGen F E (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring n k Λ m hm hgen y
  let c : v.adicCompletionIntegers F := (g : v.adicCompletionIntegers F)
  have hcz : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have hc : c ≠ 0 := by
    intro h0
    have h1 : ((c : v.adicCompletionIntegers F) : v.adicCompletion F) = 0 := by rw [h0]; rfl
    simp [c, hg] at h1
  haveI : Finite (v.adicCompletionIntegers F ⧸ Ideal.span {c}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let sec : v.adicCompletionIntegers F ⧸ Ideal.span {c} → v.adicCompletionIntegers F :=
    Function.surjInv Ideal.Quotient.mk_surjective
  have hmemf : ∀ a : Fin k → v.adicCompletionIntegers F ⧸ Ideal.span {c},
      (fun j => ∑ i, m i j ⊗ₜ[F] ((sec (a i) : v.adicCompletionIntegers F) : v.adicCompletion F)) ∈ L :=
    fun a => (key _).2 ⟨fun i => (sec (a i) : v.adicCompletion F), fun i => (sec (a i)).2, rfl⟩
  let f : (Fin k → v.adicCompletionIntegers F ⧸ Ideal.span {c}) → L ⧸ mulSub L g :=
    fun a => ((⟨_, hmemf a⟩ : L) : L ⧸ mulSub L g)
  refine Finite.of_surjective f ?_
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H y =>
  obtain ⟨a, ha, hy⟩ := (key y).1 y.2
  refine ⟨fun i => Ideal.Quotient.mk _ ⟨a i, ha i⟩, ?_⟩
  have hd : ∀ i, ∃ b : v.adicCompletionIntegers F,
      (sec (Ideal.Quotient.mk _ ⟨a i, ha i⟩) : v.adicCompletionIntegers F) = ⟨a i, ha i⟩ + b * c := by
    intro i
    have h := Function.surjInv_eq (f := Ideal.Quotient.mk (Ideal.span {c})) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk _ ⟨a i, ha i⟩)
    rw [Ideal.Quotient.eq] at h
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
    exact ⟨b, by rw [hb]; ring⟩
  choose b hb using hd
  show ((⟨_, hmemf _⟩ : L) : L ⧸ mulSub L g) = (y : L ⧸ mulSub L g)
  rw [QuotientAddGroup.eq]
  refine ⟨⟨fun j => ∑ i, m i j ⊗ₜ[F] (((-(b i)) : v.adicCompletionIntegers F) : v.adicCompletion F),
    (key _).2 ⟨_, fun i => (-(b i)).2, rfl⟩⟩, ?_⟩
  funext j
  have e1 : ∀ i, ((sec (Ideal.Quotient.mk _ ⟨a i, ha i⟩) : v.adicCompletionIntegers F) : v.adicCompletion F) =
      a i + g • (b i : v.adicCompletion F) := by
    intro i
    rw [hb i]
    simp [c, nsmul_eq_mul, mul_comm]
  have hneg : ∀ i, (((-(b i)) : v.adicCompletionIntegers F) : v.adicCompletion F) =
      -((b i : v.adicCompletionIntegers F) : v.adicCompletion F) := fun i => rfl
  rw [Submodule.coe_add, Submodule.coe_neg, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, hy]
  simp only [e1, hneg, TensorProduct.tmul_add, Finset.sum_add_distrib, TensorProduct.tmul_smul,
    TensorProduct.tmul_neg, Finset.sum_neg_distrib, Finset.smul_sum, smul_neg]
  abel

end Fin

section Gen

open Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem finiteIndex_of_princ (hc : CMData F E) (S : HSpace E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (Fin S.rank → E)) (hΛ : Module.Finite (𝓞 E) Λ) (N : ℕ) (hN : 0 < N)
    (H W : Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)))
    (hW : W ≤ levelVL hc.sig S.gram v Λ) (hH : ∀ x, InPrinc hc S v N Λ x → x ∈ H) :
    (H.subgroupOf W).FiniteIndex := by
  refine finiteIndex_of_trivOn _ N (finite_quot v Λ hΛ N hN.ne') H W (hW.trans inf_le_right) ?_
  intro x hx htriv
  apply hH
  refine ⟨hW hx, ?_⟩
  intro y hy
  obtain ⟨z, hz, e⟩ := htriv y hy
  exact ⟨z, hz, by rw [e, Nat.cast_smul_eq_nsmul]⟩

end Gen



theorem chartLoc_finiteIndex : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)).FiniteIndex := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRd hUl hchi Lb0 hLb β v hv
  have hle := GlobalTheory.T.chart_localGroup_le_baseLattice_level I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRd hUl hchi Lb0 hLb
  obtain ⟨N, hN, hpr⟩ :=
    GlobalTheory.T.chart_local_group_contains_principal_congruence I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRd hUl hchi Lb0 hLb β v hv
  have hfin : Module.Finite (𝓞 (I.rec7 l Z).host.E) Lb0 := by
    have h0 := (F u).levJ.Lb_fin
    rw [hLb] at h0
    unfold reL at h0
    refine (Module.Finite.equiv_iff (Submodule.equivMapOfInjective
      ((reV (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (I.rec7 l Z).host.E).toLinearMap.restrictScalars
        (𝓞 (I.rec7 l Z).host.E))
      (reV (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (I.rec7 l Z).host.E).injective Lb0)).mpr ?_
    exact h0
  exact finiteIndex_of_princ _ _ v Lb0 hfin N hN _ _ (iSup_le fun β' => hle β' v hv) hpr

end GlobalTheory.Mem.Col2.FinAtQ
end
end
end
