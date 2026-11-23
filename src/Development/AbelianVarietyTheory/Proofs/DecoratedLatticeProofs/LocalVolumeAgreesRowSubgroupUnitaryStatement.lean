module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsColSpaceAutToLocalGLMemOpenDense
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsN1LocalHomMemOpen
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarOpenSubgroupVolumeInvEqRelIndexStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarVolumeRatioCompactEqRelIndexRatioStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexComapEqOfCosetsHit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOpenMirabolicConjInfIntegralGLUnipotentStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOpenMirabolicProjectionToGL
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMirabolicProjectionIffColSpaceAutToLocalGL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemN1IffLocalHom
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemR1IffLocalHom
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemStabLocalizedStdLatticeIffIntegralGL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsColSpaceAutToLocalGLMemOpenDenseStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.exists_colSpaceAutToLocalGL_mem_open_dense : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M) (y : GL A k) (V : Set (GL A k)), IsOpen V → y ∈ V → ∃ x : Sp E M ≃ₗ[E] Sp E M, locHom ι e x ∈ V := by
  first | exact @GlobalTheory.denseGL_completion | exact GlobalTheory.denseGL_completion | (intros; apply GlobalTheory.denseGL_completion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsN1LocalHomMemOpenStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.exists_N1_locHom_mem_open : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) → ∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V := by
  first | exact @GlobalTheory.VolBridge.exists_N1_local_hom_mem_open | exact GlobalTheory.VolBridge.exists_N1_local_hom_mem_open | (intros; apply GlobalTheory.VolBridge.exists_N1_local_hom_mem_open <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOpenMirabolicProjectionToGLStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.isOpen_mirabolicProjectionToGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A] {c : ℕ} (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (1 : GL (A ⊕ Fin c) k) ∈ O → (∀ z ∈ R k A c 1, z ∈ O → z ∈ Ck) → IsOpen (prX Ck : Set (GL A k)) := by
  first | exact @GlobalTheory.OpenPr.isOpen_prX | exact GlobalTheory.OpenPr.isOpen_prX | (intros; apply GlobalTheory.OpenPr.isOpen_prX <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMirabolicProjectionIffColSpaceAutToLocalGLStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.mem_mirabolicProjection_iff_colSpaceAutToLocalGL : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val), (∀ x, x ∈ Loc.N1 E M c' ↔ locHom ι e x ∈ N k A c 1) → (∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V) → ∀ (CE : Subgroup (Sp E (M + c') ≃ₗ[E] Sp E (M + c'))) (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (∀ z ∈ R k A c 1, z ∈ Ck ↔ z ∈ O) → Ck ≤ R k A c 1 → (∀ x, x ∈ CE ↔ locHom ι e x ∈ Ck) → ∀ y, y ∈ Loc.prX CE ↔ locHom ι (eX e hcc he) y ∈ prX Ck := by
  first | exact @GlobalTheory.VolBridge.prX_iff_locHom | exact GlobalTheory.VolBridge.prX_iff_locHom | (intros; apply GlobalTheory.VolBridge.prX_iff_locHom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemN1IffLocalHomStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.mem_N1_iff_locHom_mem_N_one : ∀ {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) → ∀ x : Sp E (M + c') ≃ₗ[E] Sp E (M + c'), x ∈ Loc.N1 E M c' ↔ locHom ι e x ∈ N k A c 1 := by
  first | exact @GlobalTheory.UnipRead.mem_N1_iff_local_hom | exact GlobalTheory.UnipRead.mem_N1_iff_local_hom | (intros; apply GlobalTheory.UnipRead.mem_N1_iff_local_hom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemR1IffLocalHomStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.mem_R1_iff_local_hom : ∀ {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) → ∀ x : Sp E (M + c') ≃ₗ[E] Sp E (M + c'), x ∈ Loc.R1 E M c' ↔ locHom ι e x ∈ R k A c 1 := by
  first | exact @GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange | exact GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange | (intros; apply GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemStabLocalizedStdLatticeIffIntegralGLStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL : ∀ {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) → ∀ {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M) (x : Sp E M ≃ₗ[E] Sp E M), x ∈ stabL E M (stdAt E M P) ↔ locHom ι e x ∈ KO k A := by
  first | exact @GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO | exact GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO | (intros; apply GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalVolumeAgreesRowSubgroupUnitary

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.VolBridge

theorem index_comap_of_dense_image {A B : Type} [Group A] [Group B] (f : A →* B) (H : Subgroup B)
    (hf : ∀ b, ∃ a, (f a)⁻¹ * b ∈ H) : (H.comap f).index = H.index := by
  first
  | exact @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | (apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit ..)

theorem relIndex_comap_of_dense_image {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G)
    (K U : Subgroup G) (h : ∀ g ∈ U, ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) :
    (K.comap φ).relIndex (U.comap φ) = K.relIndex U := by
  let f : U.comap φ →* U := φ.subgroupComap U
  have hc : (K.comap φ).subgroupOf (U.comap φ) = (K.subgroupOf U).comap f := by
    ext x
    exact Iff.rfl
  have key := index_comap_of_dense_image f (K.subgroupOf U) (by
    rintro ⟨b, hb⟩
    obtain ⟨γ, hγK, hγU⟩ := h b hb
    have hγ : φ γ ∈ U := by
      have := U.mul_mem hb (U.inv_mem hγU)
      simpa using this
    refine ⟨⟨γ, hγ⟩, ?_⟩
    exact hγK)
  simp only [Subgroup.relIndex]
  rw [hc, key]

theorem vol_agree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → VolAgree (R := R) sel mu cst σ₀ P ι s W ν := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hok hat
  have hLev := GlobalTheory.T.parahoricLevels_characters_doubleCosets_agree_rational X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat
  haveI : ν.IsAddHaarMeasure := hν.1
  intro j c h γ g hg
  obtain ⟨e, he, hge⟩ := hg
  have hcc : cOf R j = c + 1 := by unfold cOf; have := hat.steps; omega
  have heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val := fun i => he (Sum.inr i)
  have hgφ : g = GlobalTheory.VolBridge.locHom ι e γ := Units.ext hge
  have hreg : (W.T s R).Regular := Chain.ofTwist_regular _ _ _ _ _
  obtain ⟨hJo, hJc, -⟩ := hreg.2.2 j (c + 1) h
  set J := ((W.T s R).lev j (c + 1) h).J with hJdef
  set φ := GlobalTheory.VolBridge.locHom ι e with hφ
  have hcompl := hat.compl

  have hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g) := by
    intro x
    refine ⟨e, he, ?_⟩
    rw [hgφ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by
    intro x
    rw [mem_Cgrp, ← GlobalTheory.T.mem_R1_iff_local_hom ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]
    simp [Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]
  have hN1 := GlobalTheory.T.mem_N1_iff_locHom_mem_N_one ι e hcc heR
  have hlam : lamYat (Pr := Pr) (R := R) j P.1 = stdAt X.E _ P.1 := by
    ext v
    simp only [lamYat, if_neg hat.nmem, LocE.lamY, LocE.sclLat, Submodule.mem_comap]
    congr! 1
    funext l
    simp [LocE.scE]
  have hKO : ∀ x : AutY X R j, x ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) ↔ φ x ∈ KO k _ := by
    intro x
    rw [hlam]
    exact GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL P.1 ι hcompl.int e x
  have hdN := GlobalTheory.T.exists_N1_locHom_mem_open ι hcompl.dense e hcc heR
  refine ⟨?_, ?_⟩
  ·
    have hH := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 le_rfl (by omega) ν
    haveI := hH.2.2.1
    obtain ⟨ho, hAc, hBc⟩ := GlobalTheory.T.isOpen_mirabolicConj_inf_integralGL_unipotent J g hJo hJc
    have hst : stabLat (1 : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k) = KO k _ := by
      ext z; simp [stabLat, Subgroup.mem_comap]
    have hvol : volNat ν 1 (Cgrp J g) =
        (volN ν _ (c + 1) 1 ((Cgrp J g).subgroupOf (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1) :
          Set (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1))).toReal /
        (volN ν _ (c + 1) 1 ((KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1))).subgroupOf (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1) :
          Set (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1))).toReal := by
      rw [volNat, hst]
    rw [hvol, GlobalTheory.T.haar_volume_ratio_compact_eq_relIndex_ratio _ _ _ ho hAc hBc]
    set K := Cgrp J g ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 with hKdef
    set U := KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 with hUdef
    have hA : (Cgrp J g).subgroupOf (N k _ (c + 1) 1) = K.subgroupOf (N k _ (c + 1) 1) :=
      (Subgroup.inf_subgroupOf_right _ _).symm
    have hB : (KO k _).subgroupOf (N k _ (c + 1) 1) = U.subgroupOf (N k _ (c + 1) 1) :=
      (Subgroup.inf_subgroupOf_right _ _).symm
    rw [hA, hB, Subgroup.relIndex_subgroupOf inf_le_right, Subgroup.relIndex_subgroupOf inf_le_right]
    have hKc : K.comap φ = Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ⊓ Loc.N1 X.E (R.N j) (cOf R j) := by
      ext x
      show φ x ∈ Cgrp J g ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 ↔ _
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hC, hN1]
    have hUc : U.comap φ = Loc.N1 X.E (R.N j) (cOf R j) ⊓ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) := by
      ext x
      show φ x ∈ KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 ↔ _
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hKO, hN1]; exact And.comm
    have hden : ∀ z, z ∈ K ∨ z ∈ U → ∃ x, (φ x)⁻¹ * z ∈ K ⊓ U := by
      intro z hz
      have hzN : z ∈ N k _ (c + 1) 1 := by rcases hz with hz | hz; exacts [hz.2, hz.2]
      have hO1 : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
        hJo.preimage (by fun_prop)
      have hO' := hO1.inter (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)))
      have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | v⁻¹ * z ∈ ({w | g⁻¹ * w * g ∈ J} ∩
          (KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) : Set (GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)))} :=
        hO'.preimage (by fun_prop)
      obtain ⟨x, hx, hxV⟩ := hdN z hzN _ hV (by simp [J.one_mem, one_mem])
      refine ⟨x, ?_⟩
      have hxN := (hN1 x).1 hx
      have hm : (φ x)⁻¹ * z ∈ N k _ (c + 1) 1 := mul_mem (inv_mem hxN) hzN
      have hmR : (φ x)⁻¹ * z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := by unfold GlobalTheory.RootEx.R; exact Subgroup.mem_sup_right hm
      exact ⟨⟨mem_Cgrp.2 ⟨hmR, hxV.1⟩, hm⟩, hxV.2, hm⟩
    have h1 := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ K U (fun z hz => hden z (Or.inr hz))
    have h2 := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ U K (fun z hz => by
      obtain ⟨x, hx⟩ := hden z (Or.inl hz); exact ⟨x, by rwa [inf_comm]⟩)
    rw [hKc, hUc] at h1 h2
    rw [← h1, ← h2]
    simp [Loc.volN, map_div₀, map_natCast]
  · intro hle m hm hm1
    haveI := hm
    set e' := GlobalTheory.VolBridge.eX e hcc heR with he'
    set φ' := GlobalTheory.VolBridge.locHom ι e' with hφ'
    have hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
      hJo.preimage (by fun_prop)
    have hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1, z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J} := fun z hz => by
      simp [mem_Cgrp, hz]
    have hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := fun z hz => (mem_Cgrp.1 hz).1
    have hP : ∀ y, y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ ↔ φ' y ∈ prX (Cgrp J g) :=
      GlobalTheory.T.mem_mirabolicProjection_iff_colSpaceAutToLocalGL ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC
    have hG : ∀ y, y ∈ GLint X.E (R.N j) P.1 ↔ φ' y ∈ KO k _ := fun y =>
      GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL P.1 ι hcompl.int e' y
    have hpo : IsOpen (prX (Cgrp J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)) :=
      GlobalTheory.T.isOpen_mirabolicProjectionToGL _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO)
    have hden : ∀ z, z ∈ prX (Cgrp J g) ∨ z ∈ KO k _ → ∃ y, (φ' y)⁻¹ * z ∈ prX (Cgrp J g) ⊓ KO k _ := by
      intro z _
      have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j) k | v⁻¹ * z ∈ ((prX (Cgrp J g) ⊓ KO k _ : Subgroup _) : Set _)} :=
        (hpo.inter GlobalTheory.SplitFlip.isOpen_KO).preimage (by fun_prop)
      obtain ⟨y, hy⟩ := GlobalTheory.T.exists_colSpaceAutToLocalGL_mem_open_dense ι hcompl.dense e' z _ hV (by simp [one_mem])
      exact ⟨y, hy⟩
    have hle' : prX (Cgrp J g) ≤ KO k _ := by
      intro z hz
      obtain ⟨y, hy1, hy2⟩ := hden z (Or.inl hz)
      have hyC : φ' y ∈ prX (Cgrp J g) := by
        have := mul_mem hz (inv_mem hy1); simpa using this
      have hyK : φ' y ∈ KO k _ := (hG y).1 (hle ((hP y).2 hyC))
      have := mul_mem hyK hy2; simpa using this
    have hidx := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ' (prX (Cgrp J g)) (KO k _)
      (fun z hz => hden z (Or.inr hz))
    have hc1 : (prX (Cgrp J g)).comap φ' = prCat (Pr := Pr) cst.sharp j P.1 γ := by ext y; exact (hP y).symm
    have hc2 : (KO k _).comap φ' = GLint X.E (R.N j) P.1 := by ext y; exact (hG y).symm
    rw [hc1, hc2] at hidx
    rw [hidx]
    exact GlobalTheory.T.haar_open_subgroup_volume_inv_eq_relIndex m _ _ hle' hpo GlobalTheory.SplitFlip.isCompact_KO hm1

end GlobalTheory.VolBridge
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalVolumeAgreesRowSubgroupUnitaryStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.local_volume_agrees_row_subgroup_unitary : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → VolAgree (R := R) sel mu cst σ₀ P ι s W ν := by
  first | exact @GlobalTheory.VolBridge.vol_agree | exact GlobalTheory.VolBridge.vol_agree | (intros; apply GlobalTheory.VolBridge.vol_agree <;> assumption)
end
end
