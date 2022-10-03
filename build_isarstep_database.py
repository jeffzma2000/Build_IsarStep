from isarstep_scripts.build_database import build_models

import argparse
from datetime import datetime
from pathlib import Path
from os.path import join

if __name__ == '__main__':
    def default_processed_id():
        
        now = datetime.now()
        return int("{}{}{}{}{}{}".format(now.year,now.month,now.day,now.hour,now.minute,now.second))

    parser = argparse.ArgumentParser(description='Preprocess Isabelle corpus')
    parser.add_argument('--isa_bin', type=str, default='/home/wenda/Programs/Isabelle2019/bin/isabelle',
                        help='The path of an Isabelle2019 executable')
    parser.add_argument('--isar_data', type=str, default='./isarstep_scripts/test_isar_dataset',
                        help='The path of an Isabelle corpus')
    parser.add_argument('--processed_id', type=int, default=default_processed_id(),
                        help='An integer used for resuming processing a dataset')
    args = parser.parse_args()

    build_models(args.isar_data,args.isa_bin,args.processed_id)



