# Typical exp_configs/model.yaml file structure using $\alpha \beta$ CROWN 
```
general:
  mode: verified-acc   # or: crown-only-verified-acc, etc.

model:
  name: <builtin_model_name>
  # OR: name: Customized("<your_file>.py", "<function_name>", <kwarg>=<value>, ...)
  path: <path/to/weights.pth>

data:
  dataset: <BuiltinDatasetName>
  # OR: dataset: Customized("<your_file>.py", "<loader_function_name>")
  mean: [<val>, <val>, <val>]
  std: [<val>, <val>, <val>]
  num_outputs: <int>

specification:
  type: <lp | bound>          # what kind of property you're verifying
  epsilon: <float>            # perturbation radius, if verifying robustness

attack:
  pgd_order: <before | skip>
  pgd_restarts: <int>

solver:
  batch_size: <int>
  beta-crown:
    batch_size: <int>
    iteration: <int>

bab:
  timeout: <seconds>
  max_domains: <int>
  branching:
    method: <fsb | babsr | ...>
```

## then run this in bash
```
%%bash
source activate alpha-beta-crown
python robustness_verifier.py --config exp_configs/model.yaml --start 3 --end 4
conda deactivate
```
