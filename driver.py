import argparse
import subprocess
import sys 
import datetime
import time

def main():
    parser = argparse.ArgumentParser(description='Run the checker multiple times')
    parser.add_argument("intermediate_file", type=str, help="Don't add the extension")
    parser.add_argument("spec", type=str)
    parser.add_argument("trials", type=int)
    parser.add_argument("--clear_dump_dir", action="store_true")
    parser.add_argument("--keep_successful_dumps", action="store_true")
    args = parser.parse_args()

    if args.clear_dump_dir:
        cmd = "rm output_dump/*" 
        # print(cmd)
        subprocess.call(cmd, shell=True)

    fails = 0 

    for i in range(args.trials):
        if i % 100 == 0:
            print("Running trial {0}".format(i))
        dt = datetime.datetime.now().strftime("%Y%m%d%H%M%S%f")[:-3]
        interpreter_dump = "output_dump/{0}_dump.txt".format(dt)
        intermediate_file = "output_dump/{1}_{0}.csv".format(args.intermediate_file, dt) 
        linearizability_dump = "output_dump/{0}_lin_dump.txt".format(dt)
        cmd = "dune exec _build/default/bin/main.exe {0} {1}".format(args.spec, intermediate_file)
        # print(cmd)
        with open(interpreter_dump, "w") as outfile:
            print("interpreter_dump", interpreter_dump)
            subprocess.run(cmd.split(), stdout=outfile)

        cmd = "python3 main.py {0}".format(intermediate_file)
        # print(cmd)
        with open(linearizability_dump, "w") as outfile:
            if subprocess.run(cmd.split(), stdout=outfile).returncode != 0:
                print("Failed on " + intermediate_file)
                fails = fails + 1 
            else:
                if (not args.keep_successful_dumps):
                    subprocess.call("rm {0} {1} {2}".format(interpreter_dump, intermediate_file, linearizability_dump), shell=True)
    
    print("Failed {0} out of {1} trials".format(fails, args.trials))

if __name__ == "__main__":
    sys.exit(main())