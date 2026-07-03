# Informe — lean-gaussian-field, SEGUNDO empuje del día (control final)

## Contexto

El control final detectó que este es el ÚNICO repo de la flota que ya mergeó
su empuje matinal a main (4ea3deb, heartbeat verde): base verificada para
empujar una segunda vez. La unidad elegida es el puente medida-teórico que
el frontier de la mañana dejó señalado.

## Plantilla §B2

```
HECHO:
  Rama push/m1b-realization-1d (candidato a main, 0 sorry, 0 axiom):
    RealizationOneDim.lean — PRIMER CONTENIDO MEDIDA-TEÓRICO del repo:
      realizationOneDim (gaussianReal de Mathlib con varianza alimentada
      por diag_nonneg, probado esta mañana y YA EN MAIN);
      charFun_realizationOneDim — el charFun de la medida realizadora es
      EXACTAMENTE exp(charExponent) (vía charFun_gaussianReal del pin,
      confirmado en MATHLIB_AUDIT.md del propio repo);
      exists_realization_fin_one — el patrón de realización de M1
      descargado en el caso mínimo.
    Barrel + HYPOTHESIS_FRONTIER actualizados aditivamente.
SIGUIENTE: la realización general (medidas producto + raíz cuadrada PSD)
  sigue en frontier/M1 como exists_gaussian_realization; con el caso 1-dim
  cerrado, la ruta natural es la diagonal (producto de gaussianReal) antes
  que el caso PSD general.
BLOQUEOS: ninguno.
IMPACTO-INTERFAZ: no. Interfaces.lean intacto; import aditivo en el barrel.
HONESTIDAD: (1) Es el caso MÍNIMO del patrón M1, no la realización general
  — dicho así en docstring y frontier. (2) Escrito SIN build local; CI es
  el juez, como el resto de empujes Lean de hoy.
```

## VERIFICATION — riesgos del primer build

1. `charFun_gaussianReal`: la forma exacta del exponente en el pin (orden
   t·μ vs μ·t, coeficiente v·t²/2) se absorbe con el `congr 1; push_cast;
   ring` final; si el nombre difiere:
   `grep -rn "charFun_gaussianReal" .lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/`.
2. Namespace de `charFun` (MeasureTheory vs ProbabilityTheory): cubierto
   con `open MeasureTheory ProbabilityTheory` y uso sin cualificar.
3. `NNReal.coe_mk` en el simp: si el pin usa `NNReal.val_eq_coe` u otra
   forma, añadirla al simp only.
4. La instancia `IsProbabilityMeasure (gaussianReal m v)`: existe en el pin
   (audit); `infer_instance` tras `unfold` la encuentra.

## Cómo aplicar

```bash
cd lean-gaussian-field && git fetch origin
git checkout -b push/m1b-realization-1d origin/main
git am 0001-gaussian-field-realization-1d.patch
git push -u origin push/m1b-realization-1d   # CI juzga
```
