module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SAffOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.KStability
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.DedekindSR
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.SCenOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.SLocOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CycleBoundaryInjectivity.SBridgeOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.EvaluationSums.SEvOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.FinitelyGeneratedTorsion.FgShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.FinitelyGeneratedTorsion.TensTorsion
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Assembly
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ColsMinSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ImportsAlt
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.SHeckeOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeightContinuity.SHtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.SMomOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.SPUOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrimitiveSubmatrices.PrimPush
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.RationalSuccAbove.SChainOf
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.EvaluationSums.EvhEqSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.SStokesOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.ActHomApply

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.GrpHComp

section

@[expose] public section

open CategoryTheory Simplicial UpperTheory.V.KL

theorem UpperTheory.V.KL.grpHComp :
    (∀ (G : Type) [Group G] (n : ℕ), grpHMap (MonoidHom.id G) n = 𝟙 _) ∧
      ∀ (G H K : Type) [Group G] [Group H] [Group K] (f : G →* H) (g : H →* K) (n : ℕ),
        grpHMap (g.comp f) n = grpHMap f n ≫ grpHMap g n := by
  refine ⟨fun G _ n => groupHomology.map_id n, fun G H K _ _ _ f g n => ?_⟩
  unfold grpHMap
  rw [← groupHomology.map_comp]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.BaseChangeStability.BaseChangeBijective

section

@[expose] public section

noncomputable section

open CategoryTheory UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB.StabilizationIso

theorem stab_self (R : Type) [CommRing R] (n : ℕ) (h : n ≤ n) : stab R n n h = MonoidHom.id _ := by
  refine MonoidHom.ext fun g => ?_
  ext i j
  simp [stab_apply]

theorem stab_comp (R : Type) [CommRing R] {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) (h : n ≤ k) :
    stab R n k h = (stab R m k h₂).comp (stab R n m h₁) := by
  refine MonoidHom.ext fun g => ?_
  ext i j
  simp only [MonoidHom.comp_apply, stab_apply]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

theorem isIso_stab (R : Type) [CommRing R] [IsDedekindDomain R] (i n : ℕ) (hn : 2 * i + 4 ≤ n) :
    ∀ (m : ℕ) (h : n ≤ m), IsIso (grpHMap (stab R n m h) i) := by
  intro m h
  induction m, h using Nat.le_induction with
  | base =>
    rw [stab_self, grpHComp.1]
    infer_instance
  | succ m hm ih =>
    rw [stab_comp R hm (Nat.le_succ m), grpHComp.2]
    have := PositivityTheory.v8.KStability.kStability R 2 (dedekindSR R) i m (by omega)
    infer_instance

theorem baseChange_bijective {M N : ModuleCat.{0} ℤ} (f : M ⟶ N) [IsIso f] :
    Function.Bijective (LinearMap.baseChange ℝ f.hom) := by
  have h1 : (inv f).hom ∘ₗ f.hom = LinearMap.id := by
    rw [← ModuleCat.hom_comp, IsIso.hom_inv_id, ModuleCat.hom_id]
  have h2 : f.hom ∘ₗ (inv f).hom = LinearMap.id := by
    rw [← ModuleCat.hom_comp, IsIso.inv_hom_id, ModuleCat.hom_id]
  have l1 : (LinearMap.baseChange ℝ (inv f).hom) ∘ₗ LinearMap.baseChange ℝ f.hom = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, h1, LinearMap.baseChange_id]
  have l2 : (LinearMap.baseChange ℝ f.hom) ∘ₗ LinearMap.baseChange ℝ (inv f).hom = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, h2, LinearMap.baseChange_id]
  refine ⟨Function.LeftInverse.injective (g := LinearMap.baseChange ℝ (inv f).hom) fun x => ?_,
    Function.RightInverse.surjective (g := LinearMap.baseChange ℝ (inv f).hom) fun x => ?_⟩
  · simpa using LinearMap.congr_fun l1 x
  · simpa using LinearMap.congr_fun l2 x

end PositivityTheory.KB.StabilizationIso

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.BaseChangeStability.SStabOf

section

@[expose] public section

noncomputable section

open CategoryTheory UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

theorem sStab_of : SChain → SBridge → SStab := by
  intro hC hB R _ _ k n n' h hn
  obtain ⟨θ, hsurj, hker, hnat⟩ := hB k
  have := StabilizationIso.isIso_stab R (k + 1) n (by omega) n' h
  obtain ⟨hinj, hsur⟩ := StabilizationIso.baseChange_bijective (grpHMap (stab R n n' h) (k + 1))
  have hcyc : ∀ z : Chn (GL (Fin n) R) (k + 1), IsCyc z → IsCyc (cmap (stab R n n' h) (k + 1) z) :=
    fun z hz => by
      unfold IsCyc at hz ⊢
      rw [hC.2.1, hz, map_zero]
  refine ⟨fun z hz hb => ?_, fun z' hz' => ?_⟩
  · have e := hnat _ _ (stab R n n' h) ⟨z, LinearMap.mem_ker.2 hz⟩
      ⟨_, LinearMap.mem_ker.2 (hcyc z hz)⟩ rfl
    rw [(hker _ _).2 hb] at e
    refine (hker _ ⟨z, LinearMap.mem_ker.2 hz⟩).1 (hinj ?_)
    rw [← e, map_zero]
  · obtain ⟨y, hy⟩ := hsur (θ _ ⟨z', LinearMap.mem_ker.2 hz'⟩)
    obtain ⟨w, rfl⟩ := hsurj _ y
    refine ⟨w.1, LinearMap.mem_ker.1 w.2, ?_⟩
    have e := hnat _ _ (stab R n n' h) w ⟨_, LinearMap.mem_ker.2 (hcyc w.1 (LinearMap.mem_ker.1 w.2))⟩ rfl
    exact (hker _ (⟨_, LinearMap.mem_ker.2 (hcyc w.1 (LinearMap.mem_ker.1 w.2))⟩ -
      ⟨z', LinearMap.mem_ker.2 hz'⟩)).1 (by rw [map_sub, e, hy, sub_self])

end PositivityTheory.KB

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.FinitelyGeneratedTorsion.HglFGOf

section

section

noncomputable section

open CategoryTheory NumberField

namespace UpperTheory.FiniteGenerationAndTorsion

open UpperTheory.V UpperTheory.V.KH

theorem hglFG_of (h : FgShift) : HglFG := by
  intro L _ _ hL N m
  have := hL
  let C := faceCx (KT.Gm L N) (KT.Sx L N) (KT.Sx.face L N) KT.Sx.face_smul
  have hx := KT.sx_exact L N m
  exact h (KT.Gm L N) (KT.orbBound L N m) (3 ^ (KT.dd L N * N)) m (KT.Sx L N)
    (fun p => Rep.ofHom ⟨C.d p, fun g => LinearMap.ext fun f => C.d_equiv p g f⟩)
    (Rep.trivial ℤ (KT.Gm L N) ℤ)
    (Rep.ofHom ⟨C.ε, fun g => LinearMap.ext fun f => C.ε_equiv g f⟩)
    (Nat.one_le_pow _ _ (by norm_num)) hx.1 hx.2.1 hx.2.2
    (fun p hp => ⟨(KT.orb L N p).1, (KT.orb L N p).2.trans (KT.orbBound_mono L N hp)⟩)
    (fun p _ => KT.stab L N p)

end UpperTheory.FiniteGenerationAndTorsion

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.FiniteIndexCase.SFinOf

section

section

noncomputable section

open NumberField UpperTheory.V.KT UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

theorem sFin_of : SBridge → SFin := by
  intro h L _ _ hL N k
  classical
  obtain ⟨θ, hsurj, hker, -⟩ := h k
  haveI : Module.Finite ℤ (grpH (Gm L N) (k + 1)) :=
    UpperTheory.FiniteGenerationAndTorsion.hglFG_of UpperTheory.FiniteGenerationAndTorsion.fgShift L hL N (k + 1)
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℝ (ℝ ⊗[ℤ] ↑(grpH (Gm L N) (k + 1)))).FG)
  choose pre hpre using hsurj (Gm L N)
  refine ⟨t.image (fun m => ((pre m : ↥(bd (Gm L N) k).ker) : Chn (Gm L N) (k + 1))), ?_, ?_⟩
  · intro z hz
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hz
    exact LinearMap.mem_ker.mp (pre m).2
  · intro z hz
    have hz' : z ∈ LinearMap.ker (bd (Gm L N) k) := LinearMap.mem_ker.mpr hz
    have hw : θ (Gm L N) ⟨z, hz'⟩ ∈ Submodule.span ℝ (θ (Gm L N) '' (pre '' (t : Set _))) := by
      rw [Set.image_image]
      simp only [hpre, Set.image_id']
      rw [ht]
      trivial
    rw [← Submodule.map_span] at hw
    obtain ⟨u, hu, hθ⟩ := hw
    refine ⟨(u : Chn (Gm L N) (k + 1)), ?_, ?_⟩
    · have hmem : (u : Chn (Gm L N) (k + 1)) ∈
          Submodule.map (LinearMap.ker (bd (Gm L N) k)).subtype (Submodule.span ℝ (pre '' (t : Set _))) :=
        ⟨u, hu, rfl⟩
      rw [Submodule.map_span, Set.image_image] at hmem
      simpa [Finset.coe_image] using hmem
    · have h0 : θ (Gm L N) (⟨z, hz'⟩ - u) = 0 := by
        rw [map_sub, hθ, sub_self]
      exact (hker (Gm L N) _).mp h0

end PositivityTheory.KB

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SeparationCase.SSepOf

section

section

noncomputable section

namespace PositivityTheory.KB

open ChainCochainPairing

theorem sSep : SSep := by
  intro G _ k z _ hnb
  classical
  obtain ⟨φ, hφz, hφp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnb inferInstance
  have hφ : ∀ w, φ (bd G (k + 1) w) = 0 := by
    intro w
    have hw : φ (bd G (k + 1) w) ∈ (LinearMap.range (bd G (k + 1))).map φ :=
      Submodule.mem_map_of_mem (LinearMap.mem_range_self _ w)
    rw [hφp] at hw
    exact (Submodule.mem_bot ℝ).mp hw
  refine ⟨fun y => φ (Finsupp.single (fun i : Fin (k + 1) => (y i.castSucc)⁻¹ * y i.succ) 1), ?_, ?_, ?_⟩
  · intro g y
    simp [smul_eq_mul, mul_assoc]
  · funext y
    have key : dC (fun y : Fin (k + 2) → G =>
        φ (Finsupp.single (fun i : Fin (k + 1) => (y i.castSucc)⁻¹ * y i.succ) 1)) y
        = φ (bd G (k + 1) (Finsupp.single (fun i : Fin (k + 2) => (y i.castSucc)⁻¹ * y i.succ) 1)) := by

      simp only [dC, bd, Finsupp.linearCombination_single, one_smul, map_add (f := _), map_sum, map_smul]
      rw [Fin.sum_univ_succ]
      congr 1
      · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.succ_castSucc]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Fin.val_succ, smul_eq_mul]
        congr 3
        funext l
        rcases lt_trichotomy (l : ℕ) (j : ℕ) with h | h | h
        · rw [Fin.contractNth_apply_of_lt _ _ _ _ h]
          have e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc :=
            Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; omega)
          have e2 : j.succ.succAbove l.succ = l.succ.castSucc :=
            Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; omega)
          rw [e1, e2, Fin.succ_castSucc]
        · rw [Fin.contractNth_apply_of_eq _ _ _ _ h]
          have e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc :=
            Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_iff_val_lt_val]; simp; omega)
          have e2 : j.succ.succAbove l.succ = l.succ.succ :=
            Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val]; simp; omega)
          rw [e1, e2, Fin.succ_castSucc]
          group
        · rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
          have e1 : j.succ.succAbove l.castSucc = l.castSucc.succ :=
            Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val]; simp; omega)
          have e2 : j.succ.succAbove l.succ = l.succ.succ :=
            Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val]; simp; omega)
          rw [e1, e2, Fin.succ_castSucc]
    rw [key, hφ]
    rfl
  · have hev : ev (MonoidHom.id G) (fun y : Fin (k + 2) → G =>
        φ (Finsupp.single (fun i : Fin (k + 1) => (y i.castSucc)⁻¹ * y i.succ) 1)) 1 z = φ z := by
      unfold ev
      simp only [MonoidHom.id_apply, smul_eq_mul, mul_one]
      conv_rhs => rw [← Finsupp.sum_single z]

      simp only [Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      have hg : (fun i : Fin (k + 1) => (Fin.partialProd g i.castSucc)⁻¹ * Fin.partialProd g i.succ) = g := by
        funext i
        simp [Fin.partialProd_succ]
      rw [hg, ← smul_eq_mul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hev]
    exact hφz

theorem sSep_of : SChain → SSep := fun _ => sSep

end PositivityTheory.KB
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridge

section

@[expose] public section

namespace PositivityTheory.KB

theorem sChain : SChain := sChain_of
theorem sEv : SEv := sEv_of
theorem sSep' : SSep := sSep_of sChain
theorem sBridge : SBridge := sBridge_of
theorem sStab : SStab := sStab_of sChain sBridge
theorem sFin : SFin := sFin_of sBridge
theorem sPsi : SPsi := sPsi_of sChain
theorem sAff : SAff := sAff_of sChain sEv sSep' sBridge
theorem sHecke : SHecke := sHecke_of sChain sEv sSep' sStab sFin sAff
theorem sPU : SPU := sPU_of sHt_of
theorem sMom : SMom := TwSMInt2.sMom_of sHt_of
theorem sWhit : SWhit := sWhit_of sEv sStokes_of
theorem sCen : SCen := sCen_of sEv
theorem sLoc : SLoc := sLoc_of sEv

end PositivityTheory.KB
end
end
