# Build_IsarStep

## For alternative splits of IsarStep
1. Download the [test suite of IsarStep](https://drive.google.com/file/d/1QUKC3RzzvZ5O9-VkgXx3h37heCq8OPPC/view?usp=sharing), which contains a large (about 86 GB) pre-processed repository of Isabelle proofs named ``<isar_dataset>``
2. Run the following command 
    ```
        python extract_isarstep_from_database.py --dir_in <isar_dataset> --processed_id 202092191415
    ```
    where `<isar_dataset>` refers the path to the pre-processed repository in the previous step. This will generates a repository named `extracted_isar_dataset` in the current directory, which contains the raw data points of IsarStep.

## For building IsarStep from scratch
1. We may need the following packages:
    ```
        pip install tatsu algebraic-data-types regex
    ```

2. Download the [test suite of IsarStep](https://drive.google.com/file/d/1QUKC3RzzvZ5O9-VkgXx3h37heCq8OPPC/view?usp=sharing), which contains a large (about 86 GB) pre-processed repository of Isabelle proofs named ``<isar_dataset>``. We don't need the pre-processed corpus here -- we are re-processing it. If needed, I can upload an un-processed corpus later...

3. Run the following command 
    ```
        python build_isarstep_database.py --isa_bin <Isabelle binary> --isar_data <isar_dataset>
    ```
    where `<Isabelle binary>` should be a path to a Isabelle2019 binary (e.g., /home/wenda/Programs/Isabelle2019/bin/isabelle), and `<isar_dataset>` refers the path to the pre-processed repository in the previous step. This will take about 30-40 hours on a 90-core CPU. At the end, you will get a processed repository (still within `<isar_dataset>`) and a `<processed_id>` from the standard output.

4. Run the following command 
    ```
        python extract_isarstep_from_database.py --dir_in <isar_dataset> --processed_id <processed_id>
    ```
    where `<isar_dataset>` and `<processed_id>` are from previous steps. This will generates a repository named `extracted_isar_dataset` in the current directory, which contains the raw data points of IsarStep.

