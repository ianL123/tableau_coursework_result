def compare_files(file1, file2):
    with open(file1, 'r') as f1, open(file2, 'r') as f2:
        f1_lines = f1.readlines()
        f2_lines = f2.readlines()

        # 检查行数是否相同
        if len(f1_lines) != len(f2_lines):
            print("文件行数不同")
            return False

        # 逐行对比内容
        for i, (line1, line2) in enumerate(zip(f1_lines, f2_lines), 1):
            if line1 != line2:
                print(f"第 {i} 行不同:")
                print(f"{file1}: {line1.strip()}")
                print(f"{file2}: {line2.strip()}")
                return False

    print("文件相同")
    return True

# 调用函数
compare_files('output.txt', 'outp.txt')
