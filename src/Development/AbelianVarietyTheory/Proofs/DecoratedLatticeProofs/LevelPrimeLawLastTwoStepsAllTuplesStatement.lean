module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiVacuumOperatorZeroOrLeftInvertibleStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProofStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProofStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LMLatOfLIntegral
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumAtSplitPlacesProofStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDoubleLiftAdditive
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatTensorIndicatorCharacterFacts
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLastStageCharsUnramifiedAtLevelPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAllGluedPlacesProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastKernelDatumInLastLineFrameAtLevelPrime

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.LastKerRep
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n₂ : Type} [Fintype n] [DecidableEq n] [Fintype n₂] [DecidableEq n₂]

theorem hasVal_transport {Q : Pair k n} {R : Pair k n₂} (G : Matrix n₂ n k) (G' : Matrix n n₂ k) (hGG : G * G' = 1)
    {e : n₂ → k} (he : R.HasVal e 1) (hker : ∀ y, y ∈ Q.ker ↔ G *ᵥ y ∈ R.ker) {s : 𝓀[k]ˣ}
    (hs : Q.HasVal (G' *ᵥ e) s) (y : n → k) (a : 𝓀[k]) :
    Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a) := by
  have hGe : ∀ (r : 𝒪[k]) (z : n → k), G *ᵥ (z - r • (G' *ᵥ e)) = G *ᵥ z - r • e := by
    intro r z
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]
  obtain ⟨r, hr⟩ := residue_surjective (R := 𝒪[k]) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)
  have hsr : residue 𝒪[k] r * (s : 𝓀[k]) = a := by
    rw [hr, mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
  constructor
  · intro hy
    have h1 := hy.sub (hs.smul r)
    rw [hsr, sub_self] at h1
    have h2 := Pair.mem_ker.1 ((hker _).1 (Pair.mem_ker.2 h1))
    rw [hGe] at h2
    have h3 := h2.add (he.smul r)
    rw [sub_add_cancel, zero_add, mul_one, hr] at h3
    exact h3
  · intro hy
    have h1 := hy.sub (he.smul r)
    rw [mul_one, hr, sub_self, ← hGe] at h1
    have h2 := Pair.mem_ker.1 ((hker _).2 (Pair.mem_ker.2 h1))
    have h3 := h2.add (hs.smul r)
    rw [sub_add_cancel, zero_add, hsr] at h3
    exact h3

theorem maps_transport {Q : Pair k n₂} {R : Pair k n} {n₁ : Type} [Fintype n₁] [DecidableEq n₁]
    (P : Pair k n₁) (G : Matrix n n₂ k) (s : 𝓀[k]ˣ)
    (hT : ∀ y a, Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)) (x : Matrix n₂ n₁ k) :
    Maps (s⁻¹ • P) R (G * x) ↔ Maps P Q x := by
  simp only [maps_iff_hasVal, Pair.dia_hasVal, inv_inv]
  constructor
  · intro H y a hy
    rw [hT, Matrix.mulVec_mulVec]
    apply H
    rwa [← mul_assoc, Units.mul_inv, one_mul]
  · intro H y a hy
    have := (hT _ _).1 (H y _ hy)
    rwa [← mul_assoc, Units.inv_mul, one_mul, Matrix.mulVec_mulVec] at this

theorem phiOne_transport {Q : Pair k n₂} {R : Pair k n} {n₁ : Type} [Fintype n₁] [DecidableEq n₁]
    (P : Pair k n₁) (G : Matrix n n₂ k) (s : 𝓀[k]ˣ)
    (hT : ∀ y a, Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)) (x : Matrix n₂ n₁ k) :
    phiOne (s⁻¹ • P) R (G * x) = phiOne P Q x := by
  classical
  unfold phiOne
  exact if_congr (maps_transport P G s hT x) rfl rfl

section Frames
variable {D : D7} {p : SplitPt D k} {S T : HSp D} {n' : Type} [Fintype n'] [DecidableEq n']

theorem extFun_eq_of (α : Frame p S n') (β : Frame p T n₂) (β' : Frame p T n) (Ψ : Matrix n₂ n' k → ℂ)
    (Ψ' : Matrix n n' k → ℂ) (hΨ : ∀ x, Ψ' ((β'.b' * β.b) * x) = Ψ x) : extFun α β Ψ = extFun α β' Ψ' := by
  funext t
  unfold extFun
  split_ifs
  · rw [← hΨ]
    congr 1
    unfold rd
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc β.b β.b', β.bb', Matrix.one_mul]
  · rfl

end Frames

section Lists
variable {D : D7} {ι : Type} {p : ι → SplitPt D k} {n' : Type} [Fintype n'] [DecidableEq n']

theorem overAll_of_extFun_eq (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (α : ∀ i, Frame (p i) S n')
    (β : ∀ i, Frame (p i) T n₂) (β' : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T) (Ψ : ι → Matrix n₂ n' k → ℂ)
    (Ψ' : ι → Matrix n n' k → ℂ) (h : ∀ i, extFun (α i) (β i) (Ψ i) = extFun (α i) (β' i) (Ψ' i))
    (hSB : ∀ i, Ψ' i ∈ SB (Matrix n n' k)) :
    ∀ (l : List ι) (f f' : WO S T → ℂ), OverAll ψ α β LS LT Ψ l f f' → OverAll ψ α β' LS LT Ψ' l f f' := by
  intro l f f' hf
  induction l generalizing f' with
  | nil => exact hf
  | cons i l ih =>
    change ∃ g, OverAll ψ α β LS LT Ψ l f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' at hf
    change ∃ g, OverAll ψ α β' LS LT Ψ' l f g ∧ Over ψ (α i) (β' i) LS LT g (Ψ' i) f'
    obtain ⟨g, hg, hov⟩ := hf
    refine ⟨g, ih g hg, ?_⟩
    unfold Over at hov ⊢
    obtain ⟨h1, h2, h3, -, h5⟩ := hov
    refine ⟨h1, h2, h3, hSB i, ?_⟩
    rw [← h i]
    exact h5

end Lists

theorem isLattice_of_lastKer {m : Type} [Fintype m] [DecidableEq m] {Q : Pair k n₂} (G : Matrix (m ⊕ Fin 1) n₂ k)
    (G' : Matrix n₂ (m ⊕ Fin 1) k) (hGG : G * G' = 1) (L : Submodule 𝒪[k] (m → k))
    (hker : ∀ y, y ∈ Q.ker ↔ G *ᵥ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer L) :
    L.IsFullLattice k := by
  let e : (m → k) →ₗ[k] (m ⊕ Fin 1 → k) :=
    { toFun := fun x => Sum.elim x 0
      map_add' := by intro x y; ext (i | i) <;> simp
      map_smul' := by intro c x; ext (i | i) <;> simp }
  let f : (m → k) →ₗ[k] (n₂ → k) := (Matrix.mulVecLin G').comp e
  have hGf : ∀ x, G *ᵥ f x = Sum.elim x 0 := by
    intro x
    simp only [f, e, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]
  have hf : Function.Injective f := by
    intro x y hxy
    have := congrArg (G *ᵥ ·) hxy
    simp only [hGf] at this
    funext i
    exact congrFun this (Sum.inl i)
  have hL : L = Q.ker.comap (f.restrictScalars 𝒪[k]) := by
    ext x
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, hker, hGf, GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
    simp
  rw [hL]
  have := GlobalTheory.GoodLat.isLattice_comap Q.ker Q.ker_isLat.toIsLattice f hf
  refine ⟨?_⟩
  refine eq_top_iff.2 fun x _ => ?_
  have hx : f x ∈ Submodule.span k (Q.ker : Set (n₂ → k)) := by
    rw [Submodule.IsFullLattice.span_eq_top]
    trivial
  obtain ⟨a, ha, hax⟩ := GlobalTheory.GoodLat.exists_smul_mem Q.ker hx
  have hmem : a • x ∈ Q.ker.comap (f.restrictScalars 𝒪[k]) := by
    change (f.restrictScalars 𝒪[k]) (a • x) ∈ Q.ker
    rw [map_smul]
    exact hax
  have hspan := Submodule.subset_span (R := k) hmem
  have ha' : algebraMap 𝒪[k] k a ≠ 0 := by
    intro hzero
    exact ha (IsFractionRing.injective 𝒪[k] k (hzero.trans (map_zero _).symm))
  rw [← algebraMap_smul k a x] at hspan
  simpa only [inv_smul_smul₀ ha'] using
    (Submodule.span k (Q.ker.comap (f.restrictScalars 𝒪[k]) : Set (m → k))).smul_mem
      (algebraMap 𝒪[k] k a)⁻¹ hspan

end GlobalTheory.LastKerRep


open GlobalTheory.LastKerRep in
theorem GlobalTheory.SeeSaw.lastKernel_reps :
    ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k]
      [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι),
      c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m),
      ∃ (Λ : ι → Submodule 𝒪[k] (Fin c.T.rank → k)) (hΛ : ∀ i, (Λ i).IsFullLattice k)
        (u : ι → 𝓀[k]ˣ), (∀ i, (o.γ i).IsLat v.NT (Λ i)) ∧
        Reps c.ψ (o.β (j + 1)) (o.γ₀ (j + 1 + 1) h) (c.x (j + 1)).L (c.x (j + 1 + 1)).L
          (fun i =>
            haveI := hΛ i
            phiOne (u i • o.Q (j + 1) i)
              (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastPair o.q (Λ i)))
          o.I (· ∈ v.tP) (v.dT (j + 1)) := by
  intro D c v k _ _ _ _ ι o hc hv hS j h
  have htop := fun i => (hS.pre.topT (j + 1 + 1) h i).2
  choose Λ s hLat hKer hVal using htop
  have hGG : ∀ i, ((o.γ₀ (j + 1 + 1) h i).b' * (o.β (j + 1 + 1) i).b) * ((o.β (j + 1 + 1) i).b' * (o.γ₀ (j + 1 + 1) h i).b) = 1 := by
    intro i
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (o.β (j + 1 + 1) i).b, (o.β (j + 1 + 1) i).bb', Matrix.one_mul, (o.γ₀ (j + 1 + 1) h i).b'b]
  have hΛ : ∀ i, (Λ i).IsFullLattice k := fun i => isLattice_of_lastKer _ _ (hGG i) (Λ i) (hKer i)
  refine ⟨Λ, hΛ, fun i => (s i)⁻¹, hLat, (hv.atT (j + 1)).1, fun f hf => ?_⟩
  refine overAll_of_extFun_eq c.ψ (o.β (j + 1)) (o.β (j + 1 + 1)) (o.γ₀ (j + 1 + 1) h) _ _ _ _ (fun i => ?_) (fun i => ?_)
    o.I f _ (hS.rep (j + 1) (by omega) f hf)
  · have := hΛ i
    apply extFun_eq_of
    intro x
    exact phiOne_transport _ _ _ (hasVal_transport _ _ (hGG i)
      (glue_hasVal (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.isGlue_last o.q (Λ i)))
      (fun y => (hKer i y).trans (by rw [glue_ker])) (hVal i)) x
  · have := hΛ i
    exact GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatumStatement

section

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.lastSeeSaw_combinations_operatorDatum : ∀ D : D7, GlobalTheory.FinPl.LastOp D := by
  first | exact @GlobalTheory.LastOpPf.lastOp | exact GlobalTheory.LastOpPf.lastOp | (intros; apply GlobalTheory.LastOpPf.lastOp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDoubleLiftAdditiveStatement

section

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.lastSeeSaw_doubleLift_additive : ∀ D : D7, GlobalTheory.FinPl.SeeSmall D := by
  first | exact @GlobalTheory.SeeSmallPf.seeSmall | exact GlobalTheory.SeeSmallPf.seeSmall | (intros; apply GlobalTheory.SeeSmallPf.seeSmall <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeLawLastTwoStepsAllTuples

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.TLastAll

theorem combAt_fin {D : D7} {P : Pl D → Prop} {S T : HSp D} {c : WO S T →₀ ℂ} (h : CombAt P c) : IsFinComb c := by
  intro u hu
  ext i j
  have := (Ideal.mem_inf.1 (h u hu i j)).1
  simpa using this



theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, ∀ f, IsContAut c.T f → ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ = o.mono r e (t.sBF j 0 h).χW * ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)))) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ := by
  intro D c v k _ _ _ _ ι o hc hv hS j h
  have hPl : Places o.p o.I (· ∈ v.tP) :=
    ⟨hS.pre.nodup, hS.pre.all, hS.pre.inj, hS.pre.tP, fun i => (hS.pre.char i).2⟩
  have hstd := hc.std
  have hjm : j + 1 < D.R.m := by omega
  have hx0 : IsSelfDualC _ (c.x j).L := (hc.x j (by omega)).sd
  have hx1 : IsSelfDualC _ (c.x (j + 1)).L := (hc.x (j + 1) (by omega)).sd
  have hx2 : IsSelfDualC _ (c.x (j + 1 + 1)).L := (hc.x (j + 1 + 1) (by omega)).sd
  have hpl : Nonempty (Pl D) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (α := NumberField.RingOfIntegers D.host.F)
    exact ⟨⟨M, hM.isPrime, (Ideal.bot_lt_of_maximal M (NumberField.RingOfIntegers.not_isField D.host.F)).ne'⟩⟩
  have hM : IsSelfDualC _ (o.M j 0 h) := ((hS.good (Classical.arbitrary _)).bf j 0 h).sdV₀
  obtain ⟨lam, hlam, hlamv⟩ := hS.pre.lam j h
  obtain ⟨ε', hε'⟩ := GlobalTheory.T.lastSeeSawDatumAtSplitPlaces_proof D k ι o.p o.I (· ∈ v.tP) hPl o.q c.ψ hstd o.χ o.hχ (fun i => (hS.pre.char i).1)
    (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) (Fin c.T.rank) (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1))
    (c.X (j + 1 + 1)) c.T c.Lz (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (c.bes j 0 h).ζ o.ζ₀ (c.bes j 0 h).line hS.pre.line
    (v.τ j h) lam hlam (fun i => (hlamv i).1) (hS.pre.tau j h)
  obtain ⟨Λ, hΛ, u, hγ, hrep⟩ := GlobalTheory.SeeSaw.lastKernel_reps D c v k ι o hc hv hS j h
  haveI : ∀ i, (Λ i).IsFullLattice k := hΛ
  let ε : ι → 𝓀[k]ˣ := fun i => (ε' i)⁻¹ * u i
  let Q : ι → Pair k (Fin (c.X (j + 1)).rank) := fun i => ε i • o.Q (j + 1) i
  obtain ⟨r, e, hr, hSm⟩ := GlobalTheory.T.smallPairPairingAllGluedPlaces_proof D k ι o.p o.I (· ∈ v.tP) hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) o.q o.χ o.hχ
  have hAC := GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D
  let Ψ' : ι → Matrix (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank ⊕ Fin 1) k → ℂ := fun i =>
    tensCol (phiOne (o.Q j i) (o.Q (j + 1) i)) (charInd (resChar (o.χ i) (o.hχ i) o.q) (Q i))
  have hAC1 := hAC k ι o.p o.I (· ∈ v.tP) hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank ⊕ Fin 1) c.ψ hstd
    (c.bes j 0 h).V₀ (c.X (j + 1)) (o.β₀ j 0 h) (o.β (j + 1)) (o.M j 0 h) (c.x (j + 1)).L hM hx1 Ψ'
  obtain ⟨e0, he0⟩ := hAC1.1 fun i => Comm.tensCol_mem (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _) (SBFacts.charInd_mem _ _)
  have hrep' : Reps c.ψ (o.β (j + 1)) (o.γ₀ (j + 1 + 1) h) (c.x (j + 1)).L (c.x (j + 1 + 1)).L
      (fun i => phiOne (ε' i • Q i) (lastPair o.q (Λ i))) o.I (· ∈ v.tP) (v.dT (j + 1)) := by
    have hf : (fun i => phiOne (ε' i • Q i) (lastPair o.q (Λ i))) =
        (fun i => phiOne (u i • o.Q (j + 1) i) (lastPair o.q (Λ i))) := by
      funext i
      simp only [Q, ε, smul_smul, mul_inv_cancel_left]
    rw [hf]
    exact hrep
  obtain ⟨e₁, e₂, he₁, he₂, hE⟩ := hε' (o.β j) (o.β₀ j 0 h) (o.β (j + 1)) o.γ (o.γ₀ (j + 1 + 1) h)
    (fun i => ⟨(hS.glued j 0 h i).sum, (hS.pre.topT (j + 1 + 1) h i).1⟩) Q Λ
    (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) (c.x j).L (c.x (j + 1)).L v.NT (c.x (j + 1 + 1)).L (o.M j 0 h)
    hx0 hx1 hv.sdT hx2 hM (fun i => ⟨hS.pre.latT (j + 1) (by omega) i, hγ i⟩) (v.dT j) (v.dT (j + 1))
    ⟨(hv.atT j).1, hS.rep j (by omega)⟩ hrep'
  have hLO := GlobalTheory.T.lastSeeSaw_combinations_operatorDatum D c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz
    (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (c.bes j 0 h).line.1 hS.pre.line.1 (hS.pre.tau j h)
  obtain ⟨op0, hop0, hop0e⟩ := (hLO (· ∈ v.tP)).1 e0 he0.1
  obtain ⟨op, hop, hope⟩ := ((GlobalTheory.T.biVacuumOperator_zero_or_left_invertible D) k ι o.p o.I _ hPl c.ψ hstd _ _ _ op0 hop0).2 e₁ e₂ he₁ he₂
  refine ⟨ε, op, r, e, hr, hop, ?_⟩
  intro t ht hW hU hK Ψ₁ Ψ₂ hΨ₁ hΨ₂
  obtain ⟨χA, χz, χS', χT, omz, omT', omz'', hχV, hwA, hwz, hwX, hwT, hwTi, hwz''⟩ := hW.last j h
  have hunrT := GlobalTheory.T.seesawLastStage_chars_unramified_at_levelPrime D c v k ι o hS j h t hU hK χz χS' χT hwX hwTi
  have hFV := GlobalTheory.T.flatMapPreservesVacuum_proof D c.ψ (· ∈ v.tP)
  have hΞ : Vac c.ψ (c.bes j 0 h).V₀ (c.X (j + 1)) (o.M j 0 h) (c.x (j + 1)).L (· ∈ v.tP) (flatBF (t.sBF j 0 h) Ψ₁) :=
    hFV.1 0 (c.B j 0 h) (c.J j 0 h) (t.sBF j 0 h) (v.N j) (o.M j 0 h) (v.N (j + 1)) (c.x (j + 1)).L
      (fun x _ => (hS.good x).bf j 0 h) Ψ₁ hΨ₁
  have hΦ : Vac c.ψ (c.X (j + 1)) c.T (c.x (j + 1)).L v.NT (· ∈ v.tP) (fun w => Ψ₂ ((c.jac j 0 h).d.ext0 c.T w)) :=
    hFV.2.2 (c.V (j + 1)) (c.X (j + 1)) c.T (c.jac j 0 h).d (v.N (j + 1)) (c.x (j + 1)).L v.NT (hv.sd (j + 1) hjm) hx1
      hv.sdT (fun x _ => ((hS.good x).bf j 0 h).monoW) Ψ₂ hΨ₂
  set Ξ := flatBF (t.sBF j 0 h) Ψ₁ with hΞdef
  set Φ₂ : WO (c.X (j + 1)) c.T → ℂ := fun w => Ψ₂ ((c.jac j 0 h).d.ext0 c.T w) with hΦdef
  have hΞ' := he0.2 Ξ hΞ
  obtain ⟨hBV, hEq⟩ := hE Ξ (comb c.ψ _ _ e0 Ξ) Φ₂ hΞ hΞ' hΦ
  have hlst : c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂ = lastBi (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) Ξ Φ₂ := rfl
  have hopX : op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) = biComb c.ψ _ _ _ e₁ e₂
      (lastBi (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (comb c.ψ _ _ e0 Ξ) Φ₂) := by
    rw [hope, hlst, ← hop0e]
  refine ⟨hopX ▸ hBV, ?_⟩
  intro d d' hd hd' φ hφ f hf
  rw [hopX, ← hEq]
  obtain ⟨N, a, b, hab, hdec⟩ := (hLO (· ∉ v.tP)).2 d d' hd hd'
  rw [hlst, hdec, hdec]
  have hAC2 := hAC k ι o.p o.I (· ∈ v.tP) hPl (Fin c.T.rank) (Fin (c.X (j + 1)).rank) c.ψ hstd (c.X (j + 1)) c.T
    (o.β (j + 1)) o.γ (c.x (j + 1)).L v.NT hx1 hv.sdT (fun _ _ => 0)
  have hw₁ : IsWeilDatumO c.ψ _ _ (χA * χz) (t.sBF j 0 h).χW (t.sBF j 0 h).om₀ := by
    rw [← hχV]; exact (t.sBF j 0 h).weil₀
  have hSS := GlobalTheory.T.lastSeeSaw_doubleLift_additive D c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz
    (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (c.bes j 0 h).line.1 hS.pre.line.1 (hS.pre.tau j h)
    (hc.x j (by omega)).cpt (hc.x (j + 1) (by omega)).cpt hc.cpt χA χz (t.sBF j 0 h).χW χS' χT (t.sBF j 0 h).om₀
    (t.kom j) omz (t.kom (j + 1)) omT' omz'' hw₁ hwA hwz hwX hwT hwz'' (c.x j).vol (c.x (j + 1)).vol c.volT N
  have hRam : PairDat.Ram (⟨o.β j, o.β₀ j 0 h, o.Q j⟩ : PairDat o.p (c.X j) (c.bes j 0 h).V₀ (Fin (c.X j).rank)) φ := hφ
  have hRam' := (GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D k ι o.p o.q o.χ o.hχ ε (Fin (c.X j).rank) (c.X j) (c.bes j 0 h).V₀
    ⟨o.β j, o.β₀ j 0 h, o.Q j⟩ hS.pre.inj o.I).1.mapsTo hRam
  have L1 := hSS (fun i => comb c.ψ _ _ (a i) Ξ) (fun i => comb c.ψ _ _ (b i) Φ₂)
    (fun i => ⟨((hAC1.2.2 (a i) (hab i).1 Ξ hΞ).1).1, ((hAC2.2.2 (b i) (hab i).2 Φ₂ hΦ).1).1⟩) φ f hφ.1 hf
  have L2 := hSS (fun i => comb c.ψ _ _ (a i) (comb c.ψ _ _ e0 Ξ)) (fun i => comb c.ψ _ _ (b i) Φ₂)
    (fun i => ⟨GlobalTheory.AvgMid.theta_comb hstd (combAt_fin (hab i).1) (GlobalTheory.AvgMid.theta_comb hstd (combAt_fin he0.1) hΞ.1),
      ((hAC2.2.2 (b i) (hab i).2 Φ₂ hΦ).1).1⟩) (o.S (fun _ => ε) j φ) f hRam'.1 hf
  beta_reduce at L1 L2
  unfold Comm.bl
  rw [L1, L2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hSm c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) c.T (c.bes j 0 h).o (c.bes j 0 h).ζ
    (c.bes j 0 h).line (hc.x j (by omega)).cpt (hc.x (j + 1) (by omega)).cpt hc.cpt (t.sBF j 0 h).χV (t.sBF j 0 h).χW
    χS' χT (t.sBF j 0 h).om₀ omT' (t.sBF j 0 h).weil₀ hwT
    (fun x hx => ⟨(hU.bf j 0 h x hx).1, (hU.bf j 0 h x hx).2, (hunrT x hx).1, (hunrT x hx).2⟩)
    (c.x j).vol (c.x (j + 1)).vol c.volT ⟨o.β j, o.β₀ j 0 h, o.Q j⟩ ⟨o.β (j + 1), o.Q (j + 1)⟩ ε (o.M j 0 h)
    (c.x (j + 1)).L v.NT hM hx1 hv.sdT
    (fun i => ⟨(hS.glued j 0 h i).sum, (hS.glued j 0 h i).lat, hS.pre.latT (j + 1) (by omega) i⟩)
    (comb c.ψ _ _ (a i) Ξ) (comb c.ψ _ _ (a i) (comb c.ψ _ _ e0 Ξ)) (comb c.ψ _ _ (b i) Φ₂)
    (hAC1.2.2 (a i) (hab i).1 Ξ hΞ).1 (hAC2.2.2 (b i) (hab i).2 Φ₂ hΦ).1
    ((hAC1.2.2 (a i) (hab i).1 Ξ hΞ).2 _ hΞ') φ hRam f hf

end GlobalTheory.FinPl.TLastAll

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeLawLastTwoStepsAllTuplesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.levelPrime_law_last_two_steps_all_tuples : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, ∀ f, IsContAut c.T f → ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ = o.mono r e (t.sBF j 0 h).χW * ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)))) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ := by
  first | exact @GlobalTheory.FinPl.TLastAll.main | exact GlobalTheory.FinPl.TLastAll.main | (intros; apply GlobalTheory.FinPl.TLastAll.main <;> assumption)
end
end
