module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopNorm
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.Statement
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.EqOffBound
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.Assemble
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.Bridge
public import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.GenModelXiOf
public import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.MovesComposeU
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.AdicBoxOpenness.ClosureCharacterHolds

section

@[expose] public section

noncomputable section
open scoped BigOperators
open IsDedekindDomain Topology Filter

namespace Formalism.L2.PairingIndexBounds.Rec

theorem denseInt_adic {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (w : v.adicCompletion K) (hw : Valued.v w ≤ 1) :
    w ∈ closure (Set.range fun r : R => algebraMap K (v.adicCompletion K) (algebraMap R K r)) := by
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hU
  set g := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hgdef
  have hg : g ≠ 0 := (map_ne_zero _).mpr γ.ne_zero
  have hV : {y : v.adicCompletion K | Valued.v (y - w) < g} ∈ 𝓝 w := by
    rw [Valued.mem_nhds]
    exact ⟨γ, fun y hy => by
      simp only [Set.mem_ofPred_eq] at hy ⊢
      rwa [Valuation.restrict_lt_iff_lt_embedding] at hy⟩
  have hO : ((v.adicCompletionIntegers K : ValuationSubring _) : Set (v.adicCompletion K)) ∈ 𝓝 w :=
    (Valued.isOpen_valuationSubring (v.adicCompletion K)).mem_nhds hw
  obtain ⟨_, ⟨k, rfl⟩, hk1, hk2⟩ := Dense.inter_nhds_nonempty (HeightOneSpectrum.denseRange_algebraMap K v) (inter_mem hV hO)
  have hkv : v.valuation K k ≤ 1 := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
    rw [← this]; exact hk2
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hkv (Units.mk0 g hg)
  refine ⟨algebraMap K (v.adicCompletion K) (algebraMap R K a), hγ ?_, a, rfl⟩
  simp only [Set.mem_ofPred_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hgdef]
  have e : algebraMap K (v.adicCompletion K) (algebraMap R K a) - w =
      algebraMap K (v.adicCompletion K) (algebraMap R K a - k) + (algebraMap K (v.adicCompletion K) k - w) := by
    rw [map_sub]; ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ hk1
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap R K a - k)
  rw [show algebraMap K (v.adicCompletion K) (algebraMap R K a - k) = ((algebraMap R K a - k : K) : v.adicCompletion K) from rfl, this]
  simpa using ha

theorem valAlg_adic {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem isOpen_boxW_adic {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (m n : Type) [Fintype m] [Fintype n] (t : v.adicCompletion K) :
    IsOpen {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, t * ζ i j ∈ v.adicCompletionIntegers K} := by
  have e : {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, t * ζ i j ∈ v.adicCompletionIntegers K} =
      ⋂ i, ⋂ j, (fun ζ : Matrix m n (v.adicCompletion K) => t * ζ i j) ⁻¹'
        ((v.adicCompletionIntegers K : ValuationSubring _) : Set (v.adicCompletion K)) := by
    ext ζ; simp [Set.mem_iInter]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
      (continuous_const.mul (continuous_id.matrix_elem i j))

theorem boxW_sub_closure {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) {m n : Type} (M : Set (Matrix m n K)) (d : R) (hd : d ≠ 0)
    (hM : LowB d M) :
    {ζ : Matrix m n (v.adicCompletion K) |
        ∀ i j, (algebraMap K (v.adicCompletion K) (algebraMap R K d))⁻¹ * ζ i j ∈ v.adicCompletionIntegers K} ⊆
      closure (matI v '' M) := by
  intro ζ hζ
  set e := algebraMap K (v.adicCompletion K) (algebraMap R K d) with he
  have hne : e ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd)
  let T : Set (v.adicCompletion K) := Set.range fun r : R => e * algebraMap K (v.adicCompletion K) (algebraMap R K r)
  have hT : ∀ i j, ζ i j ∈ closure T := by
    intro i j
    have h1 := denseInt_adic v _ (hζ i j)
    have h2 : ζ i j = e * (e⁻¹ * ζ i j) := by rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [h2]
    exact map_mem_closure (continuous_const.mul continuous_id) h1 (by rintro _ ⟨r, rfl⟩; exact ⟨r, rfl⟩)
  have hpi : ζ ∈ closure (Set.univ.pi fun _ : m => Set.univ.pi fun _ : n => T) := by
    rw [closure_pi_set]; intro i _; rw [closure_pi_set]; intro j _; exact hT i j
  refine closure_mono ?_ hpi
  intro ξ hξ
  choose A hA using fun i j => hξ i (Set.mem_univ _) j (Set.mem_univ _)
  refine ⟨(algebraMap R K d) • (Matrix.of A).map (algebraMap R K), hM (Matrix.of A), ?_⟩
  refine Matrix.ext fun i j => ?_
  simp only [matI, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.of_apply]
  exact hA i j

theorem low_approximation_holds : ApproxLow := by
  intro R _ _ K _ _ _ v m n _ _ M M' d hd hM' z hz
  set e := algebraMap K (v.adicCompletion K) (algebraMap R K d)
  have hU : {x | z - x ∈ {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, e⁻¹ * ζ i j ∈ v.adicCompletionIntegers K}} ∈ 𝓝 z :=
    ((isOpen_boxW_adic v m n e⁻¹).preimage (continuous_const.sub continuous_id)).mem_nhds
      (by show ∀ i j, e⁻¹ * (z - z) i j ∈ v.adicCompletionIntegers K
          intro i j; rw [sub_self, Matrix.zero_apply, mul_zero]; exact zero_mem _)
  obtain ⟨_, hx, A, hA, rfl⟩ := mem_closure_iff_nhds.mp hz _ hU
  exact ⟨A, hA, boxW_sub_closure v _ d hd hM' hx⟩

theorem closure_character_holds : ClosChar := by
  intro R _ _ K _ _ _ v m n _ _ M d hd hM y
  set e := algebraMap K (v.adicCompletion K) (algebraMap R K d) with he
  have hdK : algebraMap R K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd
  constructor
  · intro hy
    have hU : {x | matI v y - x ∈ {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, e⁻¹ * ζ i j ∈ v.adicCompletionIntegers K}} ∈ 𝓝 (matI v y) :=
      ((isOpen_boxW_adic v m n e⁻¹).preimage (continuous_const.sub continuous_id)).mem_nhds
        (by show ∀ i j, e⁻¹ * (matI v y - matI v y) i j ∈ v.adicCompletionIntegers K
            intro i j; rw [sub_self, Matrix.zero_apply, mul_zero]; exact zero_mem _)
    obtain ⟨_, hx, A, hA, rfl⟩ := mem_closure_iff_nhds.mp hy _ hU
    have hx' : ∀ p : m × n, v.valuation K ((y p.1 p.2 - A p.1 p.2) / algebraMap R K d) ≤ 1 := by
      intro p
      rw [← valAlg_adic v]
      have h := hx p.1 p.2
      have e2 : algebraMap K (v.adicCompletion K) ((y p.1 p.2 - A p.1 p.2) / algebraMap R K d) =
          e⁻¹ * (matI v y - matI v A) p.1 p.2 := by
        simp only [matI, Matrix.sub_apply, Matrix.map_apply, map_div₀, map_sub, he]
        rw [div_eq_inv_mul]
      rw [e2]; exact h
    choose nn ss hns using fun p : m × n => HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v _ (hx' p)
    refine ⟨∏ p, (ss p : R), ?_, ?_⟩
    · exact Submonoid.prod_mem _ fun p _ => (ss p).2
    · choose c hc using fun p : m × n => Finset.dvd_prod_of_mem (fun p => (ss p : R)) (Finset.mem_univ p)
      have key : (∏ p, (ss p : R)) • (y - A) =
          (algebraMap R K d) • (Matrix.of fun i j => c (i, j) * nn (i, j)).map (algebraMap R K) := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul,
          Algebra.smul_def, map_mul]
        rw [← hns (i, j), hc (i, j), map_mul]
        field_simp
      have : (∏ p, (ss p : R)) • y = (∏ p, (ss p : R)) • (y - A) + (∏ p, (ss p : R)) • A := by
        rw [smul_sub, sub_add_cancel]
      rw [this, key]
      exact M.add_mem (hM _) (M.smul_mem _ hA)
  · rintro ⟨s, hs, hsy⟩
    set es := algebraMap K (v.adicCompletion K) (algebraMap R K s) with hes
    have hs0 : s ≠ 0 := by rintro rfl; exact hs (zero_mem _)
    have hne : es ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs0)
    have hval : Valued.v es⁻¹ ≤ 1 := by
      rw [map_inv₀, hes, valAlg_adic v, HeightOneSpectrum.valuation_of_algebraMap,
        (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v s).mpr hs, inv_one]
    have h1 := denseInt_adic v _ hval
    have key := map_mem_closure (f := fun c : v.adicCompletion K => c • matI v (s • y))
      (t := matI v '' (M : Set (Matrix m n K))) (continuous_id.smul continuous_const) h1 (by
        rintro _ ⟨r, rfl⟩
        refine ⟨r • s • y, M.smul_mem r hsy, ?_⟩
        refine Matrix.ext fun i j => ?_
        simp only [matI, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul,
          Algebra.algebraMap_self, RingHom.id_apply])
    convert key using 1
    refine Matrix.ext fun i j => ?_
    simp only [matI, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul,
      Algebra.algebraMap_self, RingHom.id_apply, ← hes]
    rw [inv_mul_cancel_left₀ hne]

end Formalism.L2.PairingIndexBounds.Rec
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.ModelXiNZOf

section

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem eqOff_refl (D : D7) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : EqOff D P L L :=
  ⟨0, fun a b _ _ => ⟨fun x hx => L.smul_mem _ hx, fun x hx => L.smul_mem _ hx⟩⟩

theorem volP_self (D : D7) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {N N' : ℕ}
    (Y : AddSubgroup (Matrix (Fin N') (Fin N) (EP D P))) : volP Y Y = 1 := by
  simp [volP, AddSubgroup.addSubgroupOf_self]

theorem volA_pos {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ₀ Λ₁ : AddSubgroup V)
    (hH : IsHerm H) (hA : IsSemiChar H A α) (hB : IsSemiChar H B α) (g0 : GoodLat H α A B Λ₀)
    (g1 : GoodLat H α A B Λ₁) (hfin : relIdx Λ₀ Λ₁ ≠ 0) : 0 < volA A Λ₀ Λ₁ := by
  obtain ⟨hbc, hheis⟩ := heisU V H α A B hH hA hB
  obtain ⟨hfa, hfb⟩ := fixed_of_good H α A B Λ₀ g0 0 (fixedBy H α Λ₀).zero_mem
  obtain ⟨Xi, hXi, -⟩ := xiExists ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis
    (Λ₀.addSubgroupOf A) 0 hfa hfb
  obtain ⟨-, hpos, -⟩ := movesU V H α A B Λ₀ Λ₁ hH hA hB g0 g1 hfin 0 (fixedBy H α Λ₀).zero_mem Xi hXi
  exact hpos

theorem modelXiNZ_of (hH : HalvesRec) (D : D7) : ModelXiNZ D := by
  intro cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP th hth
  classical
  obtain ⟨hHerm, -, hIop, hTh, -⟩ := local_global_comparison_holds D (tor0 D cc δ) N N'
  let ι : Type := {q : Pair D N N' // admitted D N N' q.1 q.2 ∧ EqOff D P q.1 L₀ ∧ EqOff D P q.2 L₀'}
  have hfam := genModelXi (VC D N N') (HfS D (tor0 D cc δ) N N') (al D (tor0 D cc δ))
    (La D (tor0 D cc δ) L₀ L₀') (Matrix (Fin N') (Fin N) (EP D P)) ι
    (fun i => La D (tor0 D cc δ) i.1.1 i.1.2) (fun i => (YP D P i.1.1 i.1.2 : Set _))
    (fun i => volP (YP D P L₀ L₀') (YP D P i.1.1 i.1.2)) hHerm th (hTh _ hth) ?_
  swap
  · intro s
    obtain ⟨A, B, φ, hA, hB, g0, hs⟩ := hH D cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP
      (s.map ⟨Subtype.val, Subtype.val_injective⟩) (by
        intro q hq
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hq
        exact i.2)
    refine ⟨A, B, φ, hA, hB, g0, fun i hi => ?_⟩
    exact hs i.1 (Finset.mem_map_of_mem _ hi)
  obtain ⟨Xi, hXi⟩ := hfam
  refine ⟨Xi, ?_, ?_⟩
  · have h0 := hXi ⟨(L₀, L₀'), hAdm, eqOff_refl D P L₀, eqOff_refl D P L₀'⟩
    simp only [volP_self, Real.sqrt_one, Complex.ofReal_one, one_smul] at h0
    rw [h0]
    obtain ⟨A, B, φ, hA, hB, g0, -⟩ := hH D cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP ∅ (by simp)
    exact interSelf (VC D N N') (HfS D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) _ hHerm g0.1 th (hTh _ hth)
  · intro L L' hLL hE1 hE2
    let i : ι := ⟨(L, L'), hLL, hE1, hE2⟩
    have h1 := hXi i
    obtain ⟨A, B, φ, hA, hB, g0, hs⟩ := hH D cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP {(L, L')} (by simpa using ⟨hLL, hE1, hE2⟩)
    obtain ⟨g1, hfin, -, hvol⟩ := hs (L, L') (Finset.mem_singleton_self _)
    have hpos : 0 < volP (YP D P L₀ L₀') (YP D P L L') := by
      rw [hvol]; exact volA_pos _ _ A B _ _ hHerm hA hB g0 g1 hfin
    have hs0 : (Real.sqrt (volP (YP D P L₀ L₀') (YP D P L L')) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
    rw [hIop]
    funext z
    have h1z := congrFun h1 z
    simp only [Pi.smul_apply, smul_eq_mul] at h1z
    change Xi (Set.indicator (YP D P L L' : Set _) 1) z = _ at h1z
    rw [h1z, Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]

theorem modelXi_of (hH : HalvesRec) (D : D7) (hΔ : DiscrNZ D) : modelXi D := by
  intro cc δ hcc hδ N N' L₀ L₀' hAdm P hP th hth
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply hΔ cc hcc
    rw [← hδ, h0]
    norm_num
  exact modelXiNZ_of hH D cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP th hth

end Formalism.L2.PairingIndexBounds.Rec
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.ModelXiAll

section

@[expose] public section

namespace Formalism.L2.PairingIndexBounds.Rec

theorem modelXi_all (hH : HalvesRec) (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.modelXi D := modelXi_of hH D (discrNZ D)

end Formalism.L2.PairingIndexBounds.Rec
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.ModelXiOfParts

section

@[expose] public section

namespace Formalism.L2.PairingIndexBounds.Rec

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem HalvesRec_of (hA : HfIntRec) (hB : SelfDualRec) : HalvesRec :=
  halvesRec_of_clos closure_character_holds low_approximation_holds hA hB

theorem modelXi_of_parts (hA : HfIntRec) (hB : SelfDualRec) (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.modelXi D :=
  modelXi_all (HalvesRec_of hA hB) D

end Formalism.L2.PairingIndexBounds.Rec
end
end
