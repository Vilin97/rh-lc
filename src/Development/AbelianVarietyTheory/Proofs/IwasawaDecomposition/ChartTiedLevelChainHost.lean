module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.LocalToGlobal.Columns.Record
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Formalism.LocalToGlobal.Columns.TiedLv
public import Formalism.LocalToGlobal.Columns.TiedUpDnA
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
public import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelFunctionalEqStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeAdelicFactorisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeKeepsChart

-- Source module: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsPreDataDyadicFrame

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.PreXModel

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem embLL_tauLL (B : Base) (τ : Tau B.R) : B.embLL.comp (B.tauLL τ) = B.host.emb τ := by
  unfold Base.tauLL Host.emb
  rw [← RingHom.comp_assoc, B.embE_φ₀]

end GlobalTheory.Mem.PreXModel

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DownMoveLocalDualLatticeEqLevelPrime

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.DnLat

theorem locP_congr {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (h : p = q) (L : Submodule R W) : Formalism.HermitianLatticesTheory.localization₂ p L = Formalism.HermitianLatticesTheory.localization₂ q L := by
  subst h; rfl

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem extF_eq (M : Submodule (𝓞 E) (Fin n → E)) (P : HeightOneSpectrum (𝓞 E))
    (g : Module.Dual (Res P) (TDat.Red M P)) (y : Fin n → E) : TDat.extF M P g y = modP.ext P M g y := by
  classical
  unfold TDat.extF
  split_ifs with h
  · obtain ⟨s, hs, z, hz, hgz⟩ := h.choose_spec
    have hsy : s • y ∈ M := hz ▸ z.2
    have e := modP.ext_spec P M g y hs hsy
    have ez : z = ⟨s • y, hsy⟩ := Subtype.ext hz
    subst ez
    apply mul_left_cancel₀ (mk_ne_zero hs)
    rw [e, ← hgz]
    rfl
  · by_cases hy : ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • y ∈ M
    · exfalso
      obtain ⟨s, hs, hsy⟩ := hy
      exact h ⟨modP.ext P M g y, s, hs, ⟨s • y, hsy⟩, rfl, (modP.ext_spec P M g y hs hsy).symm⟩
    · unfold modP.ext
      rw [dite_eq_right hy]

variable {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem ok_dn_extF {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {M : Submodule (𝓞 E) (Fin n → E)}
    (hM : M = d.dnN P) (g : Module.Dual (Res P.1) (TDat.Red M P.1)) (hg : g ≠ 0) :
    (d.dn P (TDat.extF M P.1 g)).Ok := by
  subst hM
  have e : TDat.extF (d.dnN P) P.1 g = modP.ext P.1 (d.dnN P) g := funext (extF_eq _ _ g)
  rw [e]
  have hF := modP.ext_funAt P.1 (d.dnN P) g
  refine hd.dn P hP hF.add hF.smul hF.off ?_
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
    by_contra H
    push Not at H
    exact hg (LinearMap.ext H)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨x.1, x.2, by rw [modP.ext_of_mem]; exact hz⟩

theorem locP_Lsh_dn {a : 𝓞 E} (ha : SepElt ST a) {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1)
    {f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal} (hd' : (d.dn P f').Ok) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.dn P f').Lsh = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.L := by
  rw [hd'.locP_Lsh ha P]
  show Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.dnN P) = _
  rw [(hd.dnN_spec P hne).2.2.2, tud_locP_L ha ⟨d, hd⟩ P]
  exact le_antisymm
    (localization_le_of_smul_mem (one_notMem P.1) fun x hx => by rw [one_smul]; exact lv_kerAt_le ⟨d, hd⟩ ha P hx)
    (localization_le_of_smul_mem (ha.off P) fun x hx => lv_smul_LshKer_mem ⟨d, hd⟩ ha P hx)

theorem mulLat_Lsh_rep {K : Type} [Field K] [NumberField K] [StarRing K] (S : GStep E K n) (hS : S.Ok) (b : S.β) (d : S.D b)
    {γ : Matrix (Fin n) (Fin n) E} (hγ : γ = (S.gam b (S.mv b d) : Matrix (Fin n) (Fin n) E)) :
    Formalism.L2.Forms.mulLat γ (S.Lsh b (S.rep (S.cl b d))) = S.Lsh b d := by
  subst hγ
  ext x
  unfold Formalism.L2.Forms.mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := (hS.lsh_smul b (S.mv b d) (S.rep (S.cl b d)) y).2 hy
    rwa [S.mv_smul] at h
  · intro hx
    refine ⟨((S.gam b (S.mv b d))⁻¹ : GL (Fin n) E).1 *ᵥ x, ?_, ?_⟩
    · refine (hS.lsh_smul b (S.mv b d) (S.rep (S.cl b d)) _).1 ?_
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, S.mv_smul]
      exact hx
    · show (S.gam b (S.mv b d) : Matrix (Fin n) (Fin n) E) *ᵥ (((S.gam b (S.mv b d))⁻¹ : GL (Fin n) E).1 *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.Mem.Col2.DnLat


open GlobalTheory.Mem.Col2.DnLat in

theorem GlobalTheory.Mem.Col2.TC.dn_locP_lat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) → Formalism.HermitianLatticesTheory.localization₂ (PvG (I.resT l u a) v) (mulLat γ.1.1 (LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i ((I.fm l u a).dn i v c.1 g))))) = Formalism.HermitianLatticesTheory.localization₂ (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)) := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ
  obtain ⟨hg1, -, hcrd⟩ := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hlat := (hcrd u a).1
  have hPv : PvG (D := I.rec7 l Z) (I.resT l u a) v = (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal := by
    unfold PvG resT
    ext x
    exact Submodule.Quotient.mk_eq_zero _

  rw [@locP_congr _ _ _ _ _ (PvG (D := I.rec7 l Z) (I.resT l u a) v) _ (RingHom.ker_isPrime _) v.1.isPrime hPv, @locP_congr _ _ _ _ _ (PvG (D := I.rec7 l Z) (I.resT l u a) v) _ (RingHom.ker_isPrime _) v.1.isPrime hPv, hlat, hlat]
  have hdual : ∀ M : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E),
      LdG (I.rec7 l Z) i hi M = Formalism.HermitianLatticesTheory.dual (hStd (I.rec7 l Z).host.E ((I.rec7 l Z).R.N i)) M := fun M => by
    unfold LdG
    rw [hg1]
    unfold dualL
    exact rlc_span_dualSet (I.rec7 l Z).sp.cm _ M
  have hok : (I.atIn u a).Ok := l.lev u a
  have hT := hok.tied i
  have hSok : (I.stp u a i).Ok := (l.ch u a).step i
  have hmul := mulLat_Lsh_rep (I.stp u a i) hSok c.1.1 (((I.atIn u a).A i).dnPt v c.1 g) (congrArg Units.val hγ)
  have hm := moveHyp_of_ok l.pr u v
  have hMove : MoveHyp ((B.primes X).vT u) ∅ v := ⟨hm.ne, hm.st, fun w => absurd w.2 (Finset.notMem_empty _)⟩
  have hsep := sepElt_of_ok l.pr u
  have hOk := ok_dn_extF (hT.ok c.1.1 ((I.stp u a i).rep c.1)) v hMove (hT.dnN_eq c.1.1 ((I.stp u a i).rep c.1) v) g hg
  have key : Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal
      (Formalism.L2.Forms.mulLat γ.1.1 ((I.stp u a i).Lsh c.1.1
        ((I.stp u a i).rep ((I.stp u a i).cl c.1.1 (((I.atIn u a).A i).dnPt v c.1 g))))) =
      Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal (((I.atIn u a).A i).deco c.1.1 ((I.stp u a i).rep c.1)).L := by
    refine (congrArg (Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal)
      (hmul.trans ((hT.Lsh_eq _ _).trans (congrArg Deco.Lsh (hT.dn_deco _ _ _ _ hOk))))).trans ?_
    exact locP_Lsh_dn hsep (hT.ok _ _) v hMove.ne hOk
  exact (congrArg (fun M => Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal (Formalism.L2.Forms.mulLat γ.1.1 M))
    (hdual _)).trans key
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DownMoveLocalDualLatticeEqLevelPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.downMove_localDualLattice_eq_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) → Formalism.HermitianLatticesTheory.localization₂ (PvG (I.resT l u a) v) (mulLat γ.1.1 (LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i ((I.fm l u a).dn i v c.1 g))))) = Formalism.HermitianLatticesTheory.localization₂ (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)) := by
  first | exact @GlobalTheory.Mem.Col2.TC.dn_locP_lat | exact GlobalTheory.Mem.Col2.TC.dn_locP_lat | (intros; apply GlobalTheory.Mem.Col2.TC.dn_locP_lat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeAdelicFactorisationStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.moveDown_levelPrime_adelic_factorisation : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ hβ : chOf ((I.fm l u a).dn i v c.1 g) = β, ∃ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)) (η : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (κ : (K β).lev.U), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) ∧ (∀ v', v' ≠ (eV v).1 → bc (prV (E := (I.rec7 l Z).host.E) v') η.1 = 1) ∧ bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) γ.1 * ((K β).y ⟨(I.fm l u a).dn i v c.1 g, hβ⟩).1 = ((K β).y c).1 * η.1 * κ.1 ∧ ((((K β).lev.chi κ)⁻¹ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) : B.LLˣ) : B.LL) := by
  exact @GlobalTheory.Mem.Col2.DnAdel.move_down_adelic
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeKeepsChartStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.move_down_level_prime_keeps_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → chOf ((I.fm l u a).dn i v c.1 g) = β := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg
  exact GlobalTheory.Mem.Col2.TC.dn_keeps_chart I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChainHost

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DnMove



theorem gl_inv_map_mul_map {n : ℕ} {E : Type} [Field E] (φ : E →+* ℂ) (A : GL (Fin n) E) (y : Matrix (Fin n) (Fin n) ℂ) :
    ((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map φ * ((A : Matrix (Fin n) (Fin n) E).map φ * y) = y := by
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem tr_eq_of_isTr {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m)
    (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (hY : I.IdY l Z u a i hi eY) (b : (I.stp u a i).β) (g0 : (I.stp u a i).G b)
    (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi))
    (hγ : (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam b g0) (h : (I.chain l u a).Y i → ℂ) (s s' : (I.chain l u a).Y i)
    (hT : IsTr (atInf (embT (I.rec7 l Z)) γ.1.1) (eY s') (eY s)) :
    (I.stp u a i).tr B.fields.emb B.embLL b g0 h s = B.embLL (((I.stp u a i).chr b g0 : B.LLˣ) : B.LL) * h s' := by
  show B.embLL _ * h (frMul B.fields.emb B.embLL ((I.stp u a i).gam b g0)⁻¹ s) = _
  congr 2
  apply Subtype.ext
  funext τ
  have h1 := hT τ
  rw [hY, hY] at h1
  show (((I.stp u a i).gam b g0)⁻¹ : GL (Fin (B.R.N i)) B.fields.E).1.map _ * s.1 τ = s'.1 τ
  have h2 : atInf (embT (I.rec7 l Z)) (γ.1.1) τ = (((I.stp u a i).gam b g0 : GL (Fin (B.R.N i)) B.fields.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E).map (embAt B.embLL B.fields.emb τ) := by
    rw [← hγ]
    show (γ.1.1).map (embT (I.rec7 l Z) τ) = (γ.1.1).map (embAt B.embLL B.fields.emb τ)
    congr 1
    ext x
    show B.host.emb τ x = B.embLL (B.tauLL τ x)
    rw [← GlobalTheory.Mem.PreXModel.embLL_tauLL]
    rfl
  rw [h1, h2]
  exact gl_inv_map_mul_map _ _ _

theorem dnNatTieG_cols : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → DnNatTieG L eY eV K := by
  intro B X I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL
  intro v β c g hg
  have hβ := GlobalTheory.T.move_down_level_prime_keeps_chart I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg
  obtain ⟨γ, η, κ, hγ, hη, hrel, hchi⟩ := GlobalTheory.T.moveDown_levelPrime_adelic_factorisation I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg hβ
  refine ⟨hβ, γ, η, κ, hη, hrel, GlobalTheory.T.downMove_localDualLattice_eq_levelPrime I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ,
    GlobalTheory.T.move_down_level_functional_eq I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ, ?_⟩
  intro h s s' hT
  show (I.stp u a i).trTo B.fields.emb B.embLL c.1.1 (((I.atIn u a).A i).dnPt v c.1 g) h s = _
  rw [hchi]
  exact tr_eq_of_isTr I l Z u a i hi eY hY _ _ γ hγ h s s' hT

end GlobalTheory.DnMove

end
end
end
