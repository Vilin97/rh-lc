module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemLevelOfLocalDepth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDecoratedLatticeForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupGoodSetLevelsCharactersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemHeightOneSpectrumIffAdditiveValuationPos
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodParParBLast
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatPrimeNotMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParabolicCharacterEqProdSuperdiagonalSum
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeSeed
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleTwistRamifiedIffChosenPrimeOrConjHost
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDecoratedLatticeFormsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.exists_adelicReading_decoratedLatticeForms : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → (∀ i, L.βV i = 1) → Seed.FrmC.StdLat X.toD7.sp.X' → (∀ i, Seed.FrmC.StdLat (Vc X.toD7 i)) → ∀ θ : InfFam X.toD7, IsInfFam θ → ∀ MX : DSModel X.toD7.sp.X' (parB (Ptw X.toD7) X.toD7.R.m), ∃ (cX : CoefA X.toD7.sp.X') (cV : ∀ i, CoefA (Vc X.toD7 i)) (pl : PlS X.B px → Pl X.toD7.host.E) (Sb : Finset (Pl X.toD7.host.E)) (Bd : Seed.BType (famR X I hX U Xg tr) L cX cV pl) (plI : PlI X.B px → Pl X.toD7.host.E) (SF : Finset (HeightOneSpectrum (𝓞 X.toD7.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL (famR X I hX U Xg tr) L eG cX cV pl Sb Bd plI SF ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => Bd.jR t φ) ∧ ∀ i, BrgStdV X I hX U Xg tr L i (cV i) fun t φ => Bd.jL i t φ := by
  first | exact @GlobalTheory.Mem.R3.BrgRead.exists_brgL | exact GlobalTheory.Mem.R3.BrgRead.exists_brgL | (intros; apply GlobalTheory.Mem.R3.BrgRead.exists_brgL <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelsSeed

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainModels

theorem models_seed : GlobalTheory.Published.DiscreteSeriesExists → ∀ D : D7, HostHyp D → Formalism.IndefR.Seed.ModY D ∧
    ∀ (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL], (∀ x : D.host.E, ∃ y : Ks, algebraMap Ks D.what₂.LL y = D.embE x) →
      ∃ MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ),
        Formalism.IndefR.Seed.ModWAt D.what₂.embLL MW ∧ GlobalTheory.RealGeo.FrameKs Ks MW := by
  intro h D _
  exact exists_models h D

end GlobalTheory.ChainModels
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeedAtReadingKeeping

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeedChoices



theorem seed_at_reading_keeping : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (F : Face3 D A3) (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (twPl : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (ψ : AddChar (AF D.host.F) ℂ) (MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ)), L.Is A3.A.μ0 → Seed.TupL A3 L mu twPl → Seed.RecL A3 L eG → Seed.LevelsL A3 L eG F.lv2 → Seed.ModY D → Seed.ModWAt D.what₂.embLL MW → Seed.VPos D → IsStdChar D ψ (-1) → ∀ Qb : ∀ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)), (∀ t, A3.A.fam.amb.FR t → Bridge.Gf D.sp.X' → cX.W) → (∀ i t, A3.A.fam.amb.FL i t → Bridge.Gf (Vc D i) → (cV i).W) → Prop, (∀ θ : InfFam D, IsInfFam θ → ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m), ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (B : Seed.BType A3 L cX cV pl) (plI : I0 → Pl D.host.E) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL A3 L eG cX cV pl Sb B plI SF ∧ Qb cX cV (fun t φ => B.jR t φ) fun i t φ => B.jL i t φ) → ∃ R : RealDat3 D A3 Ks, R.toRealDat.toLevCh = L ∧ R.ψ = ψ ∧ R.MW = MW ∧ HEq R.eG eG ∧ R.mu = mu ∧ R.twPl = twPl ∧ Seed.PrIso R.MX R.cX R.prX ∧ R.toRealDat.Pre0 F.lv2 ∧ R.IsInert ∧ R.IsTup ∧ R.AllPlaces ∧ Qb R.cX R.cV (fun t φ => R.B.jR t φ) fun i t φ => R.B.jL i t φ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ F L eG mu twPl ψ MW hL hmu hrec hlev hY hMW hV hψ Qb hB
  obtain ⟨θ, hθ⟩ := Formalism.IndefR.Eqv.infFamExists_holds D
  obtain ⟨hMY, ⟨MX⟩⟩ := hY
  let MY := fun j => (hMY j).some
  obtain ⟨cX, cV, pl, Sb, B, plI, SF, prX, hcX, hcV, hpr, hPr, hb, hQ⟩ := hB θ hθ MX
  obtain ⟨gramR, c0R, c0L, htie⟩ := hb.tie
  have hMW' : Seed.ModWAt (D := D) (sg0 D A3.A) MW := by
    rw [show sg0 D A3.A = D.what₂.embLL from sgAt_mk _ htie.v0]; exact hMW
  let R : RealDat D A3.A Ks :=
    { toLevCh := L
      hv0 := htie.v0
      eG := eG
      pl := pl
      Sb := Sb
      θ := θ
      ψ := ψ
      MY := MY
      MX := MX
      MW := MW
      cX := cX
      cV := cV
      B := B
      prX := prX
      HX := fun _ => Seed.hZ _
      HV := fun _ _ => Seed.hZ _
      HE := Seed.hZ _
      HW := fun _ _ => Seed.hZ _
      gE := 1
      gW := fun _ _ => 1
      jX := fun _ => 0
      jV := fun _ _ => 0
      νY := fun _ _ => 0
      fdY := fun _ _ => ∅
      ν0 := 0
      fd0 := ∅
      νX := fun _ => 0
      fdX := fun _ => ∅
      νV := fun _ _ => 0
      fdV := fun _ _ => ∅
      νW := fun _ => 0
      fdW := fun _ => ∅
      ωY := fun _ _ => 1
      ωX := fun _ => 1
      ωP := fun _ _ => 1
      vac := fun _ => 0
      vacX := 0
      vacP := fun _ => 0
      vY := fun _ _ => 0
      vX := fun _ => 0
      vP := fun _ _ => 0
      ItY := fun _ => 0
      ItX := 0
      ioY := fun _ _ => 0
      ioX := fun _ => 0
      Th := fun _ => 0
      BV := fun _ _ => 0
      ioP := fun _ => 0
      thF := fun _ _ => 0
      thG := fun _ _ => 0
      nW := fun _ => 0
      FW := fun _ =>
        { WK := ⊥
          Pt := fun _ => PEmpty
          nrm := fun _ y _ => PEmpty.elim y
          nrm_nonneg := fun _ y _ => PEmpty.elim y
          nrm_zero := fun _ y => PEmpty.elim y
          nrm_add := fun _ y _ _ => PEmpty.elim y
          nrm_smul := fun _ y _ _ => PEmpty.elim y
          towKs := inferInstance
          ρ := 1
          chi := 1
          j := fun _ => 0 }
      mu := mu
      twPl := twPl
      kap := 0
      lam := fun _ _ _ _ => 0
      err0 := fun _ _ => 0 }
  refine ⟨{ toRealDat := R, plI := plI, SF := SF, lam3 := fun _ _ _ _ => 0, phs := fun _ => 1 }, rfl, rfl, rfl, HEq.rfl, rfl, rfl,
    hPr, ?_, ?_, ?_, hb.sb, hQ⟩
  · have hsub : L.Pg ⊆ Sb := by rw [hb.sb]
    exact ⟨hL, hb.red_R, hb.red_L, hlev, hrec, ⟨⟨gramR, c0R, c0L, htie⟩, hsub, hb.roots, hb.pl_onto, hb.degR, hb.degL, hb.muVal,
      hb.etaVal⟩, hθ, hV, hcX, hcV, hpr, hMW', hψ⟩
  · exact ⟨hb.in_tie, hb.in_onto, hb.in_R, hb.in_L, hb.in_SF⟩
  · exact ⟨hmu.1, hmu.2.1, hmu.2.2.1, hmu.2.2.2.1, hmu.2.2.2.2⟩

end GlobalTheory.SeedChoices
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataKeptClausesColumnChoices

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.FrameCaseLifts


open Formalism.IndefR.Seed Formalism.IndefR.Seed.Frm in
theorem frames_by_cases_lifts {D : D7} (hY : ∀ j, FrmC.StdLat (D.sp.Y j)) (hX : FrmC.StdLat D.sp.X')
    (hV : ∀ j, FrmC.StdLat (D.sp.V j)) (hW : ∀ j, 1 ≤ j → j ≤ D.R.m → FrmC.StdLat (D.sp.W j)) (Pg : Finset (Pl D.host.E)) :
    ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
      (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
      (βY : ∀ j, GL (Fin (Yc D j).rank) (Datum.EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (Datum.EAf D)),
      SDFrames ΛY (FrmP.coordL D.sp.X') (fun i => FrmP.coordL (Vc D i)) ΛW βY 1 (fun _ => 1) βW ∧
        (FramesExistDiagonal D Pg → NormalFrameConditionsDiagonal Pg βY βW) := by
  by_cases h : FramesExistDiagonal D Pg
  · obtain ⟨ΛY, -, -, ΛW, βY, -, -, βW, ⟨h1, -, -, h4⟩, h2⟩ := h
    exact ⟨ΛY, ΛW, βY, βW, ⟨h1, FrmP.isSDFrame_std _ hX 1, fun i => FrmP.isSDFrame_std _ (hV _) 1, h4⟩, fun _ => h2⟩
  · exact ⟨fun j => FrmP.coordL (Yc D j), fun i => FrmP.coordL (Wc D i), fun _ => 1, fun _ => 1,
      ⟨fun j _ => FrmP.isSDFrame_std _ (hY _) _, FrmP.isSDFrame_std _ hX 1, fun i => FrmP.isSDFrame_std _ (hV _) 1,
        fun i => FrmP.isSDFrame_std _ (hW _ (by omega) i.2) 1⟩, fun h' => absurd h' h⟩

theorem exists_levCh_tuples_of_lifts : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (T : Top.TwDat X.B) (Wt : Set X.B.places.Pl), Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) → I.Ok → Set.range I.xi = T.set I.C → SelHalf I → X.B.host.ccK = ⊤ → (∀ j, Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Seed.FrmC.StdLat (X.toD7.sp.W j))) → Seed.FrmC.StdLat X.toD7.sp.X' → ∃ (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I (usedOf I T Wt))) (mu : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → TupU I (usedOf I T Wt)) (twPl : Finset (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))), LevOf X I (usedOf I T Wt) L ∧ (Seed.Frm.FramesExistDiagonal X.toD7 L.Pg → Seed.Frm.NormalFrameConditionsDiagonal L.Pg L.βY L.βW) ∧ MuOf X I T Wt mu twPl ∧ (∀ Xg tr, Seed.TupL (famR X I hX (usedOf I T Wt) Xg tr) L mu twPl) ∧ ∀ t, ∀ P ∈ L.Q t, ((X.B.host.QS * X.B.host.q * Ideal.absNorm X.B.host.ccK : ℕ) : 𝓞 X.B.host.E) ∉ P.asIdeal := by
  intro X px I hX T Wt hWf hWc hI hrng hsel hcc hYVW hX'
  classical
  set U := usedOf I T Wt with hU
  have htw : ∀ a, Chr.IsTwist X.B.host I.S (I.xi a) := fun a =>
    (GlobalTheory.Mem.ReadTwist.isTwist_of_reads _ X.B.host _ _ _ (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have hram := GlobalTheory.Mem.Col2.RamQ.ram_iff X px I hI
  have hQr : ∀ a, ∀ PP ∈ I.Q a, ¬ (I.xi a).UnrAt PP := fun a PP h => (hram a PP).2 (Or.inl h)
  have hpl := fun a => GlobalTheory.Mem.TwistPlaces.twistPlaces X px I hI a (hQr a)
  obtain ⟨L0, h1, h2, h3, -, h4⟩ := GlobalTheory.LevelChoices.exists_levCh X.toD7 (Top.Fr.at X I.C) (TupU I U)
    (mu0F (X := X.B.fields) (tuOf I U)) (fun t => I.xi (ixOf I U t)) (fun t => I.Q (ixOf I U t))
    (hI.xi_inj.comp (ixOf_injective I U)) (by simp only [ixOf_mu0F]; exact hI.trueColumnChoices_heckeChar_reference_eq_one)
    (fun t => (htw _).1) (fun t => (htw _).2.1) (fun t => (htw _).2.2.1)
    (fun t => (hpl _).1) (fun t => (hpl _).2)
    (fun p hp => by
      have hpp : p.Prime := by
        rcases hp with rfl | rfl
        exacts [X.B.host.pde_prime, X.B.host.pde'_prime]
      obtain ⟨𝔭, h𝔭⟩ := GlobalTheory.Mem.R3.Model.exists_under_of_selHalf I hsel p hpp
      exact ⟨𝔭, fun t PP hPP hp' => h𝔭 _ PP hPP hp'⟩)
    (fun t PP => hram _ PP)
  have hPg : L0.Pg = (X.B.primes px).vGs := by
    refine Finset.ext fun P => (h4.Pg P).trans ?_
    rw [h1]
    exact (GlobalTheory.Mem.R3.Model.mem_vGs_iff I hI P).symm
  obtain ⟨ΛY, ΛW, βY, βW, hSD, hfr⟩ := frames_by_cases_lifts (D := X.toD7)
    (fun j => (hYVW j).1) hX' (fun j => (hYVW j).2.1) (fun j => (hYVW j).2.2) (X.B.primes px).vGs
  let L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U) :=
    { L0 with
      ΛY := ΛY
      ΛW := ΛW
      βY := βY
      βW := βW
      βX := 1
      βV := (fun _ => 1)
      ΛX := Formalism.IndefR.Seed.FrmP.coordL _
      ΛV := (fun _ => Formalism.IndefR.Seed.FrmP.coordL _) }
  have hLC : L.C = Top.Fr.at X I.C := h1
  have hLx : ∀ t, L.xiH t = I.xi (ixOf I U t) := fun t => congrFun h2 t
  obtain ⟨mu, twPl, hmu, htup⟩ := GlobalTheory.Mem.R3.tupL_of_twisted X px I hX T Wt L hWf hWc hI hrng hLC hLx
  refine ⟨L, mu, twPl, ⟨⟨h4.mu0, h4.eta, h4.xi, h4.xi_inj, h4.xi_base, h4.xi_fin, h4.xi_triv, h4.xi_tame, h4.Pg, h4.Q_pl,
      h4.Q_off, h4.Q_de, h4.Q_ram, h4.chi, h4.xiR, hSD.1, hSD.2.1, hSD.2.2.1, hSD.2.2.2⟩, h1, fun t => congrFun h2 t, hPg,
      fun t => congrFun h3 t, fun _ => rfl, rfl⟩, fun h => by
      show Seed.Frm.NormalFrameConditionsDiagonal L0.Pg βY βW
      rw [hPg]
      exact hfr (hPg ▸ h), hmu, htup, fun t P hP => ?_⟩
  have hP' : P ∈ I.Q (ixOf I U t) := by rw [← congrFun h3 t]; exact hP
  have hoff := ((hpl (ixOf I U t)).2 P hP').1
  intro hm
  apply hoff
  have e : Ideal.absNorm X.B.host.ccK = 1 := by rw [hcc, Ideal.absNorm_top]
  rw [e, mul_one] at hm
  have : ((X.toD7.host.QS * X.toD7.host.q * X.toD7.host.d * X.toD7.sp.T : ℕ) : 𝓞 X.toD7.host.E) =
      ((X.toD7.host.d * X.toD7.sp.T : ℕ) : 𝓞 X.toD7.host.E) * ((X.B.host.QS * X.B.host.q : ℕ) : 𝓞 X.toD7.host.E) := by
    rw [← Nat.cast_mul]
    congr 1
    change X.B.host.QS * X.B.host.q * X.B.host.d * X.B.sp.T = X.B.host.d * X.B.sp.T * (X.B.host.QS * X.B.host.q)
    ring
  rw [this]
  exact Ideal.mul_mem_left P.asIdeal _ hm



theorem exists_realDat_keep : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (T : Top.TwDat X.B)
    (Wt : Set X.B.places.Pl) (Ks' : Type) [Field Ks'] [NumberField Ks'] [Algebra Ks' X.toD7.what₂.LL],
    GlobalTheory.Published.DiscreteSeriesExists → Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) → I.Ok → Set.range I.xi = T.set I.C →
    SelHalf I → GrpAt X I → ValsIn I → HostHyp X.toD7 →
    (∀ j, Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Seed.FrmC.StdLat (X.toD7.sp.V j) ∧
      (1 ≤ j → j ≤ X.toD7.R.m → Seed.FrmC.StdLat (X.toD7.sp.W j))) → Seed.FrmC.StdLat X.toD7.sp.X' →
    (∀ i, (Vc X.toD7 i).IsPosDef) →
    (∀ x ∈ X.B.Ks, ∃ y : Ks', algebraMap Ks' X.toD7.what₂.LL y = x) →
    (∀ x : X.toD7.host.E, ∃ y : Ks', algebraMap Ks' X.toD7.what₂.LL y = X.toD7.embE x) →
    (∀ (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I (usedOf I T Wt))), L.Is (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))) →
      L.C = Top.Fr.at X I.C → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 →
        ∃ y : Ks', ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap Ks' X.toD7.what₂.LL y)) →
    ∃ (Xg : Finset (Gc X.B px → X.B.LL)) (tr₀ : TrI X.B px) (R₀ : RealDat3 X.toD7 (famR X I hX (usedOf I T Wt) Xg tr₀) Ks')
      (cG : G0 R₀.Pg X.toD7.R.r ≃* G0g X.toD7.nd),
      LevOf X I (usedOf I T Wt) R₀.toRealDat.toLevCh ∧ IsPlacewiseIdentity X (px := px) R₀.eG ∧ GoodSet X (px := px) (R₀.eG.trans cG) Xg ∧
      MuOf X I T Wt R₀.mu R₀.twPl ∧ IdemClass (D := X.toD7) (famR X I hX (usedOf I T Wt) Xg tr₀).A ∧
      R₀.toRealDat.Pre0 (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧ R₀.AllPlaces ∧
      Keep R₀.toRealDat (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 cG ∧ BrgStd X I hX (usedOf I T Wt) Xg tr₀ R₀.toRealDat := by
  intro X px I hX T Wt Ks' _ _ _ hDS hWf hWc hI hrng hsel hgrp hval hhost hYVW hX' hpos hKs hE hmuKs
  obtain ⟨L, mu, twPl, hL, hfr, hmu, htup, hq⟩ :=
    exists_levCh_tuples_of_lifts X px I hX T Wt hWf hWc hI hrng hsel X.B.ccK_top hYVW hX'
  obtain ⟨eG, cG, Xg, hid, hgood, hpsi, hc1, hc2, hrest⟩ := GlobalTheory.T.exists_finite_group_goodSet_levels_characters X px I hX (usedOf I T Wt) L hI hgrp hL
  obtain ⟨hidem, hlv, plg, iso, hp1, hp2, hp3⟩ := hrest (fun _ g => g)
  obtain ⟨hMY, hMW⟩ := GlobalTheory.ChainModels.models_seed hDS X.toD7 hhost
  obtain ⟨MW, hMW1, hMW2⟩ := hMW Ks' hE
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar X.toD7
  obtain ⟨R, e1, e2, e3, e4, e5, e6, hpr, hpre, hin, htu, hall, hstd⟩ :=
    GlobalTheory.SeedChoices.seed_at_reading_keeping X.toD7 (Gc X.B px) (PlS X.B px) (PlI X.B px) (TupU I (usedOf I T Wt))
      (famR X I hX (usedOf I T Wt) Xg (fun _ g => g)) Ks' (face0 X I hX (usedOf I T Wt) Xg (fun _ g => g)) L eG mu twPl ψ MW
      hL.is (htup _ _) ⟨eG.trans cG, plg, iso, hgood.2, hp2, hp3⟩ hlv hMY hMW1 hpos hψ
      (fun cX cV jR jL => BrgStdR X I hX (usedOf I T Wt) Xg (fun _ g => g) L cX jR ∧
        ∀ i, BrgStdV X I hX (usedOf I T Wt) Xg (fun _ g => g) L i (cV i) (jL i))
      (GlobalTheory.T.exists_adelicReading_decoratedLatticeForms X px I hX (usedOf I T Wt) Xg (fun _ g => g) L eG hI hval hL hid hL.beta.2 hL.beta.1 hX' (fun i => (hYVW _).2.1))
  subst e1
  obtain rfl := eq_of_heq e4
  subst e3 e5 e6
  refine ⟨Xg, fun _ g => g, R, cG, hL, hid, hgood, hmu, hidem, hpre, hin, htu, hall,
    ⟨hpre.std, GlobalTheory.SignsAtTypePrimes.signsAtG _ _ _ _ _ _ R.toRealDat _ cG hpre.std hpsi ⟨plg, iso, hp1, hp2, hp3⟩, hfr, hL.beta,
      hpr, ⟨plg, iso, hp1, hgood.2, hp2, hp3⟩, hpsi, ⟨fun t P hP P' hP' h => ?_, hq⟩, hmuKs _ hL.is hL.C, hMW2,
      fun p => hKs _ (hc2 p), fun g => hKs _ (hc1 g)⟩, hstd⟩
  rw [hL.Q t] at hP hP'
  exact hsel _ _ P hP P' hP' h

end GlobalTheory.Mem.R3.FrameCaseLifts

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataKeptClausesColumnChoicesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.exists_analyticData_kept_clauses_columnChoices : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (T : Top.TwDat X.B)
    (Wt : Set X.B.places.Pl) (Ks' : Type) [Field Ks'] [NumberField Ks'] [Algebra Ks' X.toD7.what₂.LL],
    GlobalTheory.Published.DiscreteSeriesExists → Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) → I.Ok → Set.range I.xi = T.set I.C →
    SelHalf I → GrpAt X I → ValsIn I → HostHyp X.toD7 →
    (∀ j, Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Seed.FrmC.StdLat (X.toD7.sp.V j) ∧
      (1 ≤ j → j ≤ X.toD7.R.m → Seed.FrmC.StdLat (X.toD7.sp.W j))) → Seed.FrmC.StdLat X.toD7.sp.X' →
    (∀ i, (Vc X.toD7 i).IsPosDef) →
    (∀ x ∈ X.B.Ks, ∃ y : Ks', algebraMap Ks' X.toD7.what₂.LL y = x) →
    (∀ x : X.toD7.host.E, ∃ y : Ks', algebraMap Ks' X.toD7.what₂.LL y = X.toD7.embE x) →
    (∀ (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I (usedOf I T Wt))), L.Is (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))) →
      L.C = Top.Fr.at X I.C → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 →
        ∃ y : Ks', ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap Ks' X.toD7.what₂.LL y)) →
    ∃ (Xg : Finset (Gc X.B px → X.B.LL)) (tr₀ : TrI X.B px) (R₀ : RealDat3 X.toD7 (famR X I hX (usedOf I T Wt) Xg tr₀) Ks')
      (cG : G0 R₀.Pg X.toD7.R.r ≃* G0g X.toD7.nd),
      LevOf X I (usedOf I T Wt) R₀.toRealDat.toLevCh ∧ IsPlacewiseIdentity X (px := px) R₀.eG ∧ GoodSet X (px := px) (R₀.eG.trans cG) Xg ∧
      MuOf X I T Wt R₀.mu R₀.twPl ∧ IdemClass (D := X.toD7) (famR X I hX (usedOf I T Wt) Xg tr₀).A ∧
      R₀.toRealDat.Pre0 (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧ R₀.AllPlaces ∧
      Keep R₀.toRealDat (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 cG ∧ BrgStd X I hX (usedOf I T Wt) Xg tr₀ R₀.toRealDat  := by
  first | exact @GlobalTheory.Mem.R3.FrameCaseLifts.exists_realDat_keep | exact GlobalTheory.Mem.R3.FrameCaseLifts.exists_realDat_keep | (intros; apply GlobalTheory.Mem.R3.FrameCaseLifts.exists_realDat_keep <;> assumption)
end
end
