import logging

logging.basicConfig(
    filename='solver.log',
    filemode='w',
    level=logging.INFO,
    format='%(asctime)s - %(filename)s - %(funcName)s - %(lineno)d\n%(message)s'
)
