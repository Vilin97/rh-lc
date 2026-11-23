module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerMapRep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiOneTameGenStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAutSpecStatement
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
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NdSpecExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeVISupIndep

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocBrOfAutSpec

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting


theorem locBr_of_autSpec_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup Sp.iq Y Cb → ∃ Br : LocBr Y, Br.nbr = Sp.nbr := by
  intro D cf jE A M C tup big X T Sp Y Cb hA
  refine ⟨⟨Sp.nbr, Sp.nbr_ind, Sp.self_good, ?_⟩, rfl⟩
  intro i w hw
  have hφ : ∀ x : X.nd.O i, iotaOQ X.nd Y.naut i x =
      (((Sp.nbr i w hw).toLL x : ↥(Sp.nbr i w hw).LL.1) : Loc.Om (X.nd.l i)) := by
    intro x
    show Y.naut.iotaQ i (algebraMap _ _ x) = _
    rw [hA.iotaQ i]
    exact Sp.nbr_iq i w hw x
  have hL := A.wd.loc (X.nd.l i) (Y.naut.iotaQC i) w hw (X.nd.O i) (Sp.nbr i w hw) (Sp.nbr_ind i w hw)
    (iotaOQ X.nd Y.naut i) hφ
  refine ⟨hφ, ?_, ?_⟩
  · intro m ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hL.1 m ρ hρ
    obtain ⟨-, e1, e2, e3, e4⟩ := hA.wdOf i m (mapRep (iotaOQ X.nd Y.naut i) ρ) w
    refine ⟨e1.trans h1, e3.trans h2, e2.trans h3, ?_⟩
    intro τ τ' hτ
    rw [show Y.naut.jumpsW i (mapRep (iotaOQ X.nd Y.naut i) ρ) τ = _ from e4 τ]
    exact h4 τ τ' hτ
  · intro LL' hLL m ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hL.2 LL' hLL m ρ hρ
    obtain ⟨-, e1, e2, e3, e4⟩ := hA.wdOf i m (mapRep (algebraMap ↥LL'.1 (Qbar (X.nd.l i))) ρ) w
    refine ⟨e1.trans h1, e3.trans h2, e2.trans h3, ?_⟩
    intro τ τ' hτ
    rw [show Y.naut.jumpsW i (mapRep (algebraMap ↥LL'.1 (Qbar (X.nd.l i))) ρ) τ = _ from e4 τ]
    exact h4 τ τ' hτ
end GlobalTheory.HeightCounting
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NdSpecExistsStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.side_rational_eigen_data_alt : GlobalTheory.Published.GlobalArtinReciprocity → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (X : LocNd (lay0 D)) (T : LocTw X), Nonempty (NdSpec A.pl M C big X T) := by
  first | exact @_root_.GlobalTheory.HeckeLocN.ndSpec_exists_alt | exact _root_.GlobalTheory.HeckeLocN.ndSpec_exists_alt | (intros; apply _root_.GlobalTheory.HeckeLocN.ndSpec_exists_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocAllExists

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting

theorem locAll_exists_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → BlocksUnique D → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam) := by
  intro hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hpsi hO hBU big
  obtain ⟨X, T, ⟨Sp⟩⟩ := _root_.GlobalTheory.T.side_rational_eigen_data_alt hGAR GlobalTheory.HeckeStdFacts.heckeStdPlain D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hO hpsi big
  obtain ⟨Y, Cb, ⟨aut⟩⟩ := _root_.GlobalTheory.T.side_rational_level_data_alt hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hpsi big X T Sp
  obtain ⟨Br, -⟩ := _root_.GlobalTheory.HeightCounting.locBr_of_autSpec_alt D cf jE A M C tp.tup big X T Sp Y Cb aut
  have hchi := _root_.GlobalTheory.T.side_rational_character_data_alt hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb big X T Sp Y Cb aut
  have hMt := _root_.GlobalTheory.HeightCounting.MtIndep.typeV_iSup_indep_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb big X T Sp Y Cb aut
  obtain ⟨Z, hbc, hrb, hmt, hss⟩ := locTy_exists D A.row A.pl X Y hBU hCheb aut.locW aut.iotaQC aut.kFbar Sp.heckeLoc_gamma_places hchi hMt
  exact ⟨{ X := X, T := T, Y := Y, C := Cb, Z := Z, B := Br, bc_tie := hbc, rbar_tie := hrb, mtpar_tie := hmt }, Sp, ⟨aut⟩, hss⟩
end GlobalTheory.HeightCounting
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocAllExistsStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.side_rational_hecke_data_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → BlocksUnique D → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam) := by
  first | exact @_root_.GlobalTheory.HeightCounting.locAll_exists_alt | exact _root_.GlobalTheory.HeightCounting.locAll_exists_alt | (intros; apply _root_.GlobalTheory.HeightCounting.locAll_exists_alt <;> assumption)
end
end
end
