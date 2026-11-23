module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksDefs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmaller
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.ActFinApply
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksAlg
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapA
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapA
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksSl

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpand

section

@[expose] public section

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.CuspRep

namespace GlobalTheory.LeviGL.ZGood

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem zalg_commute {z z' : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (hz' : z' ∈ Zalg E a) : Commute z z' :=
  GlobalTheory.AutGrowth.KilledFin.Zalg_commute hz hz'

end GlobalTheory.LeviGL.ZGood

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapB

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem rel_expand (G : Sm E (r + s)) (hu : ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), G.1 (unip x * g) = G.1 g)
    (τ : E →+* ℂ) (c : ℂ → ℂ) (hcap : ∀ u, cap τ u G = c u • G) {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s)
    (hG : ∀ p, G.1 (lev (Ad E) r s p) = ∑ i, (b i).1 p.1 * (q i).1 p.2) (u : ℂ) (p : GA E r × GA E s) :
    ∑ i, (cap τ (u - (s : ℂ) / 2) (b i)).1 p.1 * (cap τ (u + (r : ℂ) / 2) (q i)).1 p.2 =
      c u * ∑ i, (b i).1 p.1 * (q i).1 p.2 := by
  have h1 := CapFactor.cap_levi E r s τ u G hu p
  rw [hcap] at h1
  have hH : ∀ p', (capR r s τ (u - (s : ℂ) / 2) G).1 (lev (Ad E) r s p') =
      ∑ i, (cap τ (u - (s : ℂ) / 2) (b i)).1 p'.1 * (q i).1 p'.2 :=
    fun p' => capR_expand (n := ![r, s]) τ _ G b q hG p'
  have h2 := capS_expand (n := ![r, s]) τ (u + (r : ℂ) / 2) (capR r s τ (u - (s : ℂ) / 2) G)
    (fun i => cap τ (u - (s : ℂ) / 2) (b i)) q hH p
  rw [← hG p]
  change c u * G.1 _ = _ at h1
  rw [h1]
  exact h2.symm

theorem tensL_apply (N : ℕ) (f : ℕ → Module.End ℂ (Sm E r)) (u : ℂ) {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s) :
    (∑ j ∈ Finset.range N, u ^ j • tensOp (f j) LinearMap.id) (fun p : GA E r × GA E s => ∑ i, (b i).1 p.1 * (q i).1 p.2) =
      fun p => ∑ i, ((∑ j ∈ Finset.range N, u ^ j • f j) (b i)).1 p.1 * (q i).1 p.2 := by
  funext p
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, tensOp_sum, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, LinearMap.id_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem tensR_apply (N : ℕ) (f : ℕ → Module.End ℂ (Sm E s)) (u : ℂ) {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s) :
    (∑ j ∈ Finset.range N, u ^ j • tensOp LinearMap.id (f j)) (fun p : GA E r × GA E s => ∑ i, (b i).1 p.1 * (q i).1 p.2) =
      fun p => ∑ i, (b i).1 p.1 * ((∑ j ∈ Finset.range N, u ^ j • f j) (q i)).1 p.2 := by
  funext p
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, tensOp_sum, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, LinearMap.id_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem fd_tens2 (Z₁ : Submodule ℂ (Sm E r)) (Z₂ : Submodule ℂ (Sm E s)) [FiniteDimensional ℂ Z₁]
    [FiniteDimensional ℂ Z₂] : FiniteDimensional ℂ (tens2 Z₁ Z₂) := by
  classical
  let B₁ := Module.finBasis ℂ Z₁
  let B₂ := Module.finBasis ℂ Z₂
  let f : Fin (Module.finrank ℂ Z₁) × Fin (Module.finrank ℂ Z₂) → (GA E r × GA E s → ℂ) :=
    fun ij m => (B₁ ij.1).1.1 m.1 * (B₂ ij.2).1.1 m.2
  have hle : tens2 Z₁ Z₂ ≤ Submodule.span ℂ (Set.range f) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    have e₁ := B₁.sum_repr ⟨φ₁, h₁⟩
    have e₂ := B₂.sum_repr ⟨φ₂, h₂⟩
    have e : (fun m : GA E r × GA E s => φ₁.1 m.1 * φ₂.1 m.2) =
        ∑ ij : Fin (Module.finrank ℂ Z₁) × Fin (Module.finrank ℂ Z₂), (B₁.repr ⟨φ₁, h₁⟩ ij.1 * B₂.repr ⟨φ₂, h₂⟩ ij.2) • f ij := by
      funext m
      have a₁ := congrArg (fun x : Z₁ => x.1.1 m.1) e₁
      have a₂ := congrArg (fun x : Z₂ => x.1.1 m.2) e₂
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at a₁ a₂
      change φ₁.1 m.1 * φ₂.1 m.2 = _
      rw [← a₁, ← a₂, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact Submodule.sum_mem _ fun ij _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij, rfl⟩)
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) := FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  exact Submodule.finiteDimensional_of_le hle

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapD

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem decomp_G (G : Sm E (r + s))
    (hu : ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), G.1 (unip x * g) = G.1 g)
    (mm : (E →+* ℂ) → Multiset ℂ) (hmm : ∀ τ, (mm τ).Nodup)
    (hcap : ∀ τ u, cap τ u G = ((mm τ).map (u + ·)).prod • G)
    {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s) (hb : ∀ i, IsAutForm (b i)) (hq : ∀ i, IsAutForm (q i))
    (hG : ∀ p, G.1 (lev (Ad E) r s p) = ∑ i, (b i).1 p.1 * (q i).1 p.2) :
    ∃ (S : Finset ((E →+* ℂ) → Multiset ℂ)) (x : ((E →+* ℂ) → Multiset ℂ) → (GA E r × GA E s → ℂ)),
      (∀ p, G.1 (lev (Ad E) r s p) = ∑ σ ∈ S, x σ p) ∧
      ∀ σ ∈ S, (∀ τ, σ τ ≤ mm τ ∧ Multiset.card (σ τ) = r) ∧
        (∀ m₂, ∃ θ ∈ zspan b, (∀ y, x σ (y, m₂) = θ.1 y) ∧
          ∀ τ w, cap τ w θ = ((σ τ).map (fun z => w + (s : ℂ) / 2 + z)).prod • θ) ∧
        (∀ m₁, ∃ θ ∈ zspan q, (∀ y, x σ (m₁, y) = θ.1 y) ∧
          ∀ τ w, cap τ w θ = ((mm τ - σ τ).map (fun z => w - (r : ℂ) / 2 + z)).prod • θ) := by
  classical
  have := zspan_fd b hb
  have := zspan_fd q hq
  have := fd_tens2 (zspan b) (zspan q)
  have ca := fun τ : E →+* ℂ => cap_coeff (E := E) r τ (-(s : ℂ) / 2)
  choose fa ha1 haZ haeq using ca
  have cb := fun τ : E →+* ℂ => cap_coeff (E := E) s τ ((r : ℂ) / 2)
  choose fb hb1 hbZ hbeq using cb
  let AA : (E →+* ℂ) → ℕ → Module.End ℂ (GA E r × GA E s → ℂ) := fun τ j => tensOp (fa τ j) LinearMap.id
  let BB : (E →+* ℂ) → ℕ → Module.End ℂ (GA E r × GA E s → ℂ) := fun τ j => tensOp LinearMap.id (fb τ j)
  let v : GA E r × GA E s → ℂ := fun p => ∑ i, (b i).1 p.1 * (q i).1 p.2
  have hAW : ∀ τ j, ∀ w ∈ tens2 (zspan b) (zspan q), AA τ j w ∈ tens2 (zspan b) (zspan q) := by
    intro τ j w hw
    obtain ⟨n, ψ₁, ψ₂, h₁, h₂, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp (fa τ j) LinearMap.id _ ∈ _
    rw [tensOp_sum]
    exact A.sum_mem (fun i => zspan_stable b (haZ τ j) _ (h₁ i)) (fun i => h₂ i)
  have hBW : ∀ τ j, ∀ w ∈ tens2 (zspan b) (zspan q), BB τ j w ∈ tens2 (zspan b) (zspan q) := by
    intro τ j w hw
    obtain ⟨n, ψ₁, ψ₂, h₁, h₂, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp LinearMap.id (fb τ j) _ ∈ _
    rw [tensOp_sum]
    exact A.sum_mem (fun i => h₁ i) (fun i => zspan_stable q (hbZ τ j) _ (h₂ i))
  have hAA : ∀ τ j τ' l, ∀ w ∈ tens2 (zspan b) (zspan q), AA τ j (AA τ' l w) = AA τ' l (AA τ j w) := by
    intro τ j τ' l w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp (fa τ j) LinearMap.id (tensOp (fa τ' l) LinearMap.id _) =
      tensOp (fa τ' l) LinearMap.id (tensOp (fa τ j) LinearMap.id _)
    rw [tensOp_sum, tensOp_sum, tensOp_sum, tensOp_sum]
    funext p
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Module.End.mul_apply, (GlobalTheory.LeviGL.ZGood.zalg_commute (haZ τ j) (haZ τ' l)).eq, Module.End.mul_apply]
  have hAB : ∀ τ j τ' l, ∀ w ∈ tens2 (zspan b) (zspan q), AA τ j (BB τ' l w) = BB τ' l (AA τ j w) := by
    intro τ j τ' l w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp (fa τ j) LinearMap.id (tensOp LinearMap.id (fb τ' l) _) =
      tensOp LinearMap.id (fb τ' l) (tensOp (fa τ j) LinearMap.id _)
    rw [tensOp_sum, tensOp_sum, tensOp_sum, tensOp_sum]
    rfl
  have hBB : ∀ τ j τ' l, ∀ w ∈ tens2 (zspan b) (zspan q), BB τ j (BB τ' l w) = BB τ' l (BB τ j w) := by
    intro τ j τ' l w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp LinearMap.id (fb τ j) (tensOp LinearMap.id (fb τ' l) _) =
      tensOp LinearMap.id (fb τ' l) (tensOp LinearMap.id (fb τ j) _)
    rw [tensOp_sum, tensOp_sum, tensOp_sum, tensOp_sum]
    funext p
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Module.End.mul_apply (fb τ j), (GlobalTheory.LeviGL.ZGood.zalg_commute (hbZ τ j) (hbZ τ' l)).eq, Module.End.mul_apply]
  have hA1 : ∀ τ, ∀ w ∈ tens2 (zspan b) (zspan q), AA τ r w = w := by
    intro τ w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp (fa τ r) LinearMap.id _ = _
    rw [tensOp_sum, ha1 τ]
    rfl
  have hB1 : ∀ τ, ∀ w ∈ tens2 (zspan b) (zspan q), BB τ s w = w := by
    intro τ w hw
    obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hw
    change tensOp LinearMap.id (fb τ s) _ = _
    rw [tensOp_sum, hb1 τ]
    rfl
  have hv : v ∈ tens2 (zspan b) (zspan q) := A.sum_mem (fun i => mem_zspan b i) (fun i => mem_zspan q i)
  have hrel : ∀ τ (u : ℂ), (∑ j ∈ Finset.range (r + 1), u ^ j • AA τ j) ((∑ l ∈ Finset.range (s + 1), u ^ l • BB τ l) v) =
      ((mm τ).map (u + ·)).prod • v := by
    intro τ u
    change (∑ j ∈ Finset.range (r + 1), u ^ j • tensOp (fa τ j) LinearMap.id)
      ((∑ l ∈ Finset.range (s + 1), u ^ l • tensOp LinearMap.id (fb τ l)) v) = _
    rw [tensR_apply, ← hbeq τ u, tensL_apply, ← haeq τ u]
    funext p
    have e : u + -(s : ℂ) / 2 = u - (s : ℂ) / 2 := by ring
    rw [e, rel_expand G hu τ (fun u => ((mm τ).map (u + ·)).prod) (hcap τ) b q hG u p]
    rfl
  obtain ⟨S, x, hxW, hsum, hprop⟩ := BlockAlgebra.decomp r s AA BB mm (tens2 (zspan b) (zspan q)) hAW hBW hAA hAB hBB
    hA1 hB1 hmm v hv hrel
  refine ⟨S, x, fun p => ?_, fun σ hσ => ⟨fun τ => ⟨(hprop σ hσ τ).1, (hprop σ hσ τ).2.1⟩, fun m₂ => ?_, fun m₁ => ?_⟩⟩
  · rw [hG]
    change v p = _
    rw [hsum, Finset.sum_apply]
  · obtain ⟨n, ψ₁, ψ₂, h₁, -, hx⟩ := tensor_pair_finite_sum (hxW σ hσ)
    refine ⟨∑ i, (ψ₂ i).1 m₂ • ψ₁ i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i),
      fun y => by rw [hx]; simp [Finset.sum_apply, mul_comm], fun τ w => ?_⟩
    have key := ((hprop σ hσ τ).2.2 (w + (s : ℂ) / 2)).1
    change (∑ j ∈ Finset.range (r + 1), (w + (s : ℂ) / 2) ^ j • tensOp (fa τ j) LinearMap.id) (x σ) = _ at key
    rw [hx, tensL_apply, ← haeq τ] at key
    have e : w + (s : ℂ) / 2 + -(s : ℂ) / 2 = w := by ring
    rw [e] at key
    refine Subtype.ext (funext fun y => ?_)
    have k2 := congrFun key (y, m₂)
    simp only [Pi.smul_apply, smul_eq_mul] at k2

    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    simp only [mul_comm ((ψ₂ _).1 m₂)] at k2 ⊢
    rw [k2, Finset.mul_sum]
  · obtain ⟨n, ψ₁, ψ₂, -, h₂, hx⟩ := tensor_pair_finite_sum (hxW σ hσ)
    refine ⟨∑ i, (ψ₁ i).1 m₁ • ψ₂ i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i),
      fun y => by rw [hx]; simp [Finset.sum_apply], fun τ w => ?_⟩
    have key := ((hprop σ hσ τ).2.2 (w - (r : ℂ) / 2)).2
    change (∑ j ∈ Finset.range (s + 1), (w - (r : ℂ) / 2) ^ j • tensOp LinearMap.id (fb τ j)) (x σ) = _ at key
    rw [hx, tensR_apply, ← hbeq τ] at key
    have e : w - (r : ℂ) / 2 + (r : ℂ) / 2 = w := by ring
    rw [e] at key
    refine Subtype.ext (funext fun y => ?_)
    have k2 := congrFun key (m₁, y)
    simp only [Pi.smul_apply, smul_eq_mul] at k2

    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [k2, Finset.mul_sum]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapE

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Eig {a : ℕ} (L : Submodule ℂ (Sm E a)) (σ : (E →+* ℂ) → Multiset ℂ) (sh : ℂ) : Submodule ℂ (Sm E a) where
  carrier := {φ | φ ∈ L ∧ ∀ τ w, cap τ w φ = ((σ τ).map (fun z => w + sh + z)).prod • φ}
  add_mem' := fun {φ ψ} hφ hψ => ⟨L.add_mem hφ.1 hψ.1, fun τ w => by rw [map_add (f := _), hφ.2, hψ.2, smul_add]⟩
  zero_mem' := ⟨L.zero_mem, fun τ w => by rw [map_zero, smul_zero]⟩
  smul_mem' := fun c φ hφ => ⟨L.smul_mem c hφ.1, fun τ w => by rw [map_smul, hφ.2, smul_comm]⟩

def adm (mm : (E →+* ℂ) → Multiset ℂ) (n : ℕ) : Finset ((E →+* ℂ) → Multiset ℂ) := by
  classical
  exact Fintype.piFinset fun τ => ((mm τ).powerset.filter fun σ => Multiset.card σ = n).toFinset

theorem mem_adm {mm : (E →+* ℂ) → Multiset ℂ} {n : ℕ} {σ : (E →+* ℂ) → Multiset ℂ} :
    σ ∈ adm mm n ↔ ∀ τ, σ τ ≤ mm τ ∧ Multiset.card (σ τ) = n := by
  classical
  unfold adm
  rw [Fintype.mem_piFinset]
  refine forall_congr' fun τ => ?_
  rw [Multiset.mem_toFinset, Multiset.mem_filter, Multiset.mem_powerset]

variable {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

theorem LS_zalg (hU : IsAutSt U) (hT : IsSliceMap U c T) : ∀ z ∈ Zalg E r, ∀ φ ∈ LS U T, z φ ∈ LS U T :=
  fun _ hz φ hφ => Zalg_stable (fun X => BlockSlices.LS_stable hU hT (.lie X)) hz φ hφ

theorem RS_zalg (hU : IsAutSt U) (hT : IsSliceMap U c T) : ∀ z ∈ Zalg E s, ∀ φ ∈ RS U T, z φ ∈ RS U T :=
  fun _ hz φ hφ => Zalg_stable (fun X => BlockSlices.RS_stable hU hT (.lie X)) hz φ hφ

theorem data_one (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) {ψ : Sm E (r + s)} (hψ : ψ ∈ U) :
    (∀ τ u, cap τ u (T ψ) = ((mm τ).map (u + ·)).prod • T ψ) ∧
    ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s), (∀ i, b i ∈ LS U T) ∧ (∀ i, q i ∈ RS U T) ∧
      ∀ p, (T ψ).1 (lev (Ad E) r s p) = ∑ i, (b i).1 p.1 * (q i).1 p.2 := by
  refine ⟨fun τ u => ?_, ?_⟩
  · have hI : ∀ X, ∀ φ ∈ U, lie E (r + s) X φ ∈ U := fun X φ hφ => hU.1 (.lie X) φ hφ
    rw [← (BlockSlices.zalg_comm hI T hT.equiv (cap_mem_Zalg τ u) ψ hψ).2, (hinf τ).2 u ψ hψ, map_smul]
  · obtain ⟨n, b, q, hb, hq, he⟩ := BlockSlices.expand hU hT ψ hψ 1 1
    refine ⟨n, b, q, fun i => ?_, fun i => rsF_sub_RS hψ 1 1 (hq i), fun p => ?_⟩
    · exact (Submodule.span_le.2 (lsF_sub_LS hψ 1 1)) (hb i)
    · rw [← he p, BlockSlices.yp_one, mul_one]

theorem LS_le_iSup (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ) (hmm : ∀ τ, (mm τ).Nodup)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) :
    LS U T ≤ ⨆ σ ∈ adm mm r, Eig (LS U T) σ ((s : ℂ) / 2) := by
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₂, hℓ⟩
  obtain ⟨ψ', hψ', e⟩ := BlockSlices.base_one hU hT hψ k g
  obtain ⟨hcap, n, b, q, hb, hq, hG⟩ := data_one hU hT mm hinf hψ'
  obtain ⟨S, x, hsum, hS⟩ := decomp_G (T ψ') (hT.unipInv ψ' hψ') mm hmm hcap b q
    (fun i => BlockSlices.LS_aut hT _ (hb i)) (fun i => BlockSlices.RS_aut hT _ (hq i)) hG
  have hz := zspan_le b hb (LS_zalg hU hT)
  choose θ hθ hθx hθe using fun σ (hσ : σ ∈ S) => (hS σ hσ).2.1 m₂
  have hℓ' : ℓ = ∑ σ ∈ S.attach, θ σ.1 σ.2 := by
    refine Subtype.ext (funext fun m₁ => ?_)
    rw [hℓ, ← e, hsum, Submodule.coe_sum, Finset.sum_apply, ← Finset.sum_attach S]
    exact Finset.sum_congr rfl fun σ _ => hθx σ.1 σ.2 m₁
  rw [SetLike.mem_coe, hℓ']
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hadm : σ.1 ∈ adm mm r := mem_adm.2 (hS σ.1 σ.2).1
  exact Submodule.mem_iSup_of_mem σ.1 (Submodule.mem_iSup_of_mem hadm ⟨hz (hθ σ.1 σ.2), hθe σ.1 σ.2⟩)

theorem RS_le_iSup (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ) (hmm : ∀ τ, (mm τ).Nodup)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) :
    RS U T ≤ ⨆ ρ ∈ adm mm s, Eig (RS U T) ρ (-(r : ℂ) / 2) := by
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₁, hℓ⟩
  obtain ⟨ψ', hψ', e⟩ := BlockSlices.base_one hU hT hψ k g
  obtain ⟨hcap, n, b, q, hb, hq, hG⟩ := data_one hU hT mm hinf hψ'
  obtain ⟨S, x, hsum, hS⟩ := decomp_G (T ψ') (hT.unipInv ψ' hψ') mm hmm hcap b q
    (fun i => BlockSlices.LS_aut hT _ (hb i)) (fun i => BlockSlices.RS_aut hT _ (hq i)) hG
  have hz := zspan_le q hq (RS_zalg hU hT)
  choose θ hθ hθx hθe using fun σ (hσ : σ ∈ S) => (hS σ hσ).2.2 m₁
  have hℓ' : ℓ = ∑ σ ∈ S.attach, θ σ.1 σ.2 := by
    refine Subtype.ext (funext fun m₂ => ?_)
    rw [hℓ, ← e, hsum, Submodule.coe_sum, Finset.sum_apply, ← Finset.sum_attach S]
    exact Finset.sum_congr rfl fun σ _ => hθx σ.1 σ.2 m₂
  rw [SetLike.mem_coe, hℓ']
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hadm : (fun τ => mm τ - σ.1 τ) ∈ adm mm s := mem_adm.2 fun τ => by
    refine ⟨Multiset.sub_le_self _ _, ?_⟩
    rw [Multiset.card_sub ((hS σ.1 σ.2).1 τ).1, (hinf τ).1, ((hS σ.1 σ.2).1 τ).2]
    omega
  refine Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hadm ⟨hz (hθ σ.1 σ.2), fun τ w => ?_⟩)
  rw [hθe σ.1 σ.2 τ w]
  congr 3
  funext z
  ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
end
end
